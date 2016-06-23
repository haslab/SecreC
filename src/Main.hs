{-# LANGUAGE FlexibleContexts, ViewPatterns, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}

module Main where

import qualified Data.List as List
import Data.List.Split
import Data.Either
import Data.Version (showVersion)

import Language.SecreC.Pretty as Pretty
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Modules
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Transformation.Simplify
import Language.SecreC.Transformation.Default
import Language.SecreC.Transformation.Dafny

import System.Console.CmdArgs
import System.Environment
import System.FilePath
import System.IO
import System.Posix.Escape
import System.Process
import System.Exit

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Except
import Control.Monad.Reader as Reader

import Text.PrettyPrint hiding (mode,Mode(..))

import Paths_SecreC

-- * main function

main :: IO ()
main = do
    opts <- getOpts
    case opts of
        Opts  {} -> secrec opts

-- * front-end options

printHelp :: IO ()
printHelp = withArgs ["--help"] $ cmdArgsRun mode >> return ()

mode  :: Mode (CmdArgs Options)
mode  = cmdArgsMode $
           modes [optionsDecl &= auto]
        &= help "SecreC analyser"
        &= summary ("secrec " ++ showVersion version ++ " \n\
                   \(C) PRACTICE TEAM 2016 - DI/HasLab - Univ. Minho,\
                   \ Braga, Portugal")

getOpts :: IO Options
getOpts = getArgs >>= doGetOpts
    where 
    doGetOpts as
        | null as   = withArgs ["--help"] $ cmdArgsRun mode >>= addImportPaths >>= return . processOpts
        | otherwise = cmdArgsRun mode >>= addImportPaths >>= return . processOpts

addImportPaths :: Options -> IO Options
addImportPaths opts = do
    p1 <- getDataFileName "imports"
    p2 <- getDataFileName ("imports" </> "stdlib" </> "lib")
    return $ opts { paths = p1 : p2 : paths opts }

parsePaths :: [FilePath] -> [FilePath]
parsePaths = concatMap (splitOn ":")

dafnyPrelude :: IO FilePath
dafnyPrelude = getDataFileName ("imports" </> "prelude.dfy")

-- back-end code

data OutputType = OutputFile FilePath | OutputStdout | NoOutput
  deriving (Show,Read,Data,Typeable,Eq)

defaultOutputType = NoOutput

-- | Set output mode for processed modules:
-- * inputs with explicit output files write to the file
-- * inputs without explicit output files write to stdout
-- * non-input modules do not output
resolveOutput :: [FilePath] -> [FilePath] -> [TypedModuleFile] -> IO [(TypedModuleFile,OutputType)]
resolveOutput inputs outputs modules = do
    inputs' <- mapM canonicalPath inputs
    let db = zipLeft inputs' outputs
    let res (Left (time,ppargs,m)) = case List.lookup (moduleFile m) db of
            Just (Just o) -> return (Left (time,ppargs,m),OutputFile o) -- input with matching output
            Just Nothing -> return (Left (time,ppargs,m),OutputStdout) -- intput without matching output
            Nothing -> do
                return (Left (time,ppargs,m),NoOutput) -- non-input loaded module
        res (Right sci) = do
            return (Right sci,NoOutput)
    mapM res modules

passes :: [FilePath] -> [FilePath] -> [ModuleFile] -> SecrecM IO ()
passes secrecIns secrecOuts modules = runTcM $ failTcM (noloc::Position) $ localOptsTcM (\opts -> opts { failTypechecker = False }) $ do
    tc <- typecheck modules
    case tc of
        Nothing -> return ()
        Just typedModules -> do
            opts <- askOpts
            outputModules <- liftIO $ output secrecIns secrecOuts typedModules
            verifyDafny outputModules

typecheck :: [ModuleFile] -> TcM IO (Maybe [TypedModuleFile])
typecheck modules = do
    opts <- askOpts
    let printMsg str = liftIO $ putStrLn $ show $ text "Modules" <+> Pretty.sepBy (char ',') (map (text . moduleId . thr3) $ lefts $ modules) <+> text str <> char '.'
    if (typeCheck opts)
        then do
            modules' <- mapM defaultModuleFile modules
            --liftIO $ putStrLn $ show $ text "defaults" <+> vcat (map (\(Left (x,y,z)) -> pp z) $ filter (either (const True) (const False)) modules')
            typedModules <- mapM (tcModuleFile) modules'
            printMsg "are well-typed"
            return $ Just typedModules
        else do
            printMsg "parsed OK" 
            return Nothing

verifyDafny :: [(TypedModuleFile,OutputType)]  -> TcM IO ()
verifyDafny files = do
    opts <- askOpts
    when (verify opts) $ do
        let dfyfile = "out.dfy"
        let dfylfile = "out_leak.dfy"
        let bplfile = "out.bpl"
        let bplfile2 = "out_axiom.bpl"
        let bpllfile = "out_leak.bpl"
        let bpllfile2 = "out_leak_axiom.bpl"
        liftIO $ putStrLn $ show $ text "Generating Dafny output file" <+> text (show dfyfile)
        prelude <- liftIO dafnyPrelude
        es <- getEntryPoints files
        (dfy,axs) <- toDafny prelude False es
        liftIO $ writeFile dfyfile (show dfy)
        liftIO $ putStrLn $ show $ text "Generating Dafny output leakage file" <+> text (show dfylfile)
        (dfyl,axsl) <- toDafny prelude True es
        liftIO $ writeFile dfylfile (show dfyl)
        compileDafny dfyfile bplfile
        axiomatizeBoogaman axs bplfile bplfile2
        runBoogie bplfile2
        compileDafny dfylfile bpllfile
        shadowBoogaman axsl bpllfile bpllfile2
        runBoogie bpllfile2

command :: (MonadIO m,MonadError SecrecError m) => String -> m ()
command cmd = do
    liftIO $ putStrLn $ "Running command " ++ show cmd
    exit <- liftIO $ system cmd
    case exit of
        ExitSuccess -> return ()
        ExitFailure err -> genError noloc $ int err

compileDafny :: (MonadIO m,MonadError SecrecError m) => FilePath -> FilePath -> m ()
compileDafny dfy bpl = do
    liftIO $ putStrLn $ show $ text "Compiling Dafny file" <+> text (show dfy)
    command $ "dafny /compile:0 " ++ dfy ++ " /print:" ++ bpl ++ " /noVerify"

axiomatizeBoogaman :: (MonadIO m,MonadError SecrecError m) => [String] -> FilePath -> FilePath -> m ()
axiomatizeBoogaman axioms bpl1 bpl2 = do
    liftIO $ putStrLn $ show $ text "Axiomatizing boogie file" <+> text (show bpl1) <+> text "into" <+> text (show bpl2) 
    let addaxiom x = text "--axioms=" <> text (escape x)
    command $ show $ text "boogaman" <+> text bpl1
        <+> Pretty.sepBy space (map addaxiom axioms)
        <+> text ">" <+> text bpl2
    
shadowBoogaman :: (MonadIO m,MonadError SecrecError m) => [String] -> FilePath -> FilePath -> m ()
shadowBoogaman axioms bpl1 bpl2 = do
    liftIO $ putStrLn $ show $ text "Shadowing boogie file" <+> text (show bpl1) <+> text "into" <+> text (show bpl2) 
    let addaxiom x = text "--axioms=" <> text (escape x)
    command $ show $ text "boogaman" <+> text bpl1
        <+> text "--vcgen=dafny"
        <+> text "--filterleakage=true"
        <+> text "--shadow"
        <+> Pretty.sepBy space (map addaxiom $ axioms ++ map (++".shadow") axioms)
        <+> text ">" <+> text bpl2

runBoogie :: (MonadIO m,MonadError SecrecError m) => FilePath -> m ()
runBoogie bpl = do
    liftIO $ putStrLn $ show $ text "Verifying Boogie file" <+> text (show bpl)
    command $ show $ text "boogie /doModSetAnalysis" <+> text bpl

getEntryPoints :: [(TypedModuleFile,OutputType)] -> TcM IO [DafnyId]
getEntryPoints files = do
    opts <- askOpts
    case entryPoints opts of
        (List.null -> True) -> do
            let files' = map fst $ filter ((/=NoOutput) . snd) files
            liftM concat $ mapM entryPointsTypedModuleFile files'
        es -> mapM resolveEntryPoint es

output :: [FilePath] -> [FilePath] -> [TypedModuleFile] -> IO [(TypedModuleFile,OutputType)] 
output secrecIns secrecOuts modules = do
    moduleso <- resolveOutput secrecIns secrecOuts modules
    forM_ moduleso $ \(mfile,o) -> case mfile of
        Left (time,ppargs,m) -> case o of
            NoOutput -> do
                hPutStrLn stderr $ "No output for module " ++ show (moduleFile m)
                return ()
            OutputFile f -> writeFile f $ show $ pp ppargs $+$ pp m
            OutputStdout -> do
                putStrLn $ show (moduleFile m) ++ ":"
                putStrLn $ show $ pp ppargs $+$ pp m
        Right sci -> do
            hPutStrLn stderr $ "No output for unchanged module " ++ show (sciFile sci)
            return ()
    return moduleso

secrec :: Options -> IO ()
secrec opts = do
    let secrecIns = inputs opts
    let secrecOuts = outputs opts
    when (List.null secrecIns) $ throwError $ userError "no SecreC input files"
    runSecrecM opts $ do
        modules <- parseModuleFiles secrecIns
        passes secrecIns secrecOuts modules
        

