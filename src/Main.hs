{-# LANGUAGE ViewPatterns, DeriveDataTypeable #-}
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
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Transformation.Simplify
import Language.SecreC.Transformation.Dafny

import System.Console.CmdArgs
import System.Environment
import System.FilePath
import System.IO

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

dafnyLeakagePrelude :: IO FilePath
dafnyLeakagePrelude = getDataFileName ("imports" </> "leakage.dfy")

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
            typedModules <- mapM tcModuleFile modules
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
        liftIO $ putStrLn $ show $ text "Generating Dafny output file" <+> text (show dfyfile)
        leakagePrelude <- liftIO dafnyLeakagePrelude
        es <- getEntryPoints files
        (dfy,axs) <- toDafny leakagePrelude False es
        (dfyl,axsl) <- toDafny leakagePrelude True es
        liftIO $ writeFile dfyfile (show dfy)
        liftIO $ writeFile dfylfile (show dfyl)

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
        

