{-# LANGUAGE FlexibleContexts, ViewPatterns, DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}

module Main where

import qualified Data.List as List
import Data.List.Split
import Data.Either
import Data.Version (showVersion)
import Data.Maybe
import qualified Data.Text as Text
import Data.Generics
import qualified Data.Set as Set
import Data.Set (Set(..))

import Language.SecreC.IO
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
import Control.Monad.State as State

import Control.Concurrent.Async

import Text.PrettyPrint hiding (mode,Mode(..))
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as Parsec
import qualified Text.ParserCombinators.Parsec.Number as Parsec

import Paths_SecreC

import Debug.Trace

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
    let res (Left (time,ppargs,m,ml)) = case List.lookup (moduleFile m) db of
            Just (Just o) -> return (Left (time,ppargs,m,ml),OutputFile o) -- input with matching output
            Just Nothing -> return (Left (time,ppargs,m,ml),OutputStdout) -- intput without matching output
            Nothing -> do
                return (Left (time,ppargs,m,ml),NoOutput) -- non-input loaded module
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
            outputModules <- liftIO $ output opts secrecIns secrecOuts typedModules
            verifyDafny outputModules

typecheck :: [ModuleFile] -> TcM IO (Maybe [TypedModuleFile])
typecheck modules = flushTcWarnings $ do
    opts <- askOpts
    let printMsg str = liftIO $ putStrLn $ show $ text "Modules" <+> Pretty.sepBy (char ',') (map (text . moduleId . thr4) $ lefts $ modules) <+> text str <> char '.'
    if (typeCheck opts)
        then do
            modules' <- if defaults opts
                then mapM defaultModuleFile modules
                else return modules
            debugTc $ do
                x <- mapM (\(Left (x,y,z,w)) -> pp z) $ filter (either (const True) (const False)) modules'
                liftIO $ putStrLn $ show $ text "defaults" <+> vcat x
            typedModules <- mapM (tcModuleFile) modules'
            printMsg "are well-typed"
            return $ Just typedModules
        else do
            printMsg "parsed OK" 
            return Nothing

verifyOpts :: [(TypedModuleFile,OutputType)] -> Options
verifyOpts = mconcat . map (ppOptions . either snd4 sciPPArgs . fst)

verifyDafny :: [(TypedModuleFile,OutputType)]  -> TcM IO ()
verifyDafny files = localOptsTcM (`mappend` verifyOpts files) $ do
    opts <- askOpts
    when (verify opts /= NoneV) $ do
        let dfyfile = "out.dfy"
        let dfylfile = "out_leak.dfy"
        let bplfile = "out.bpl"
        let bplfile2 = "out_axiom.bpl"
        let bpllfile = "out_leak.bpl"
        let bpllfile2 = "out_leak_product.bpl"
        
        -- generate dafny files
        when (debugVerification opts) $ liftIO $ hPutStrLn stderr $ show $ text "Generating Dafny output file" <+> text (show dfyfile)
        prelude <- liftIO dafnyPrelude
        es <- getEntryPoints files
        (dfy,axs) <- toDafny prelude False es
        liftIO $ writeFile dfyfile (show dfy)
        when (debugVerification opts) $ liftIO $ hPutStrLn stderr $ show $ text "Generating Dafny output leakage file" <+> text (show dfylfile)
        (dfyl,axsl) <- toDafny prelude True es
        liftIO $ writeFile dfylfile (show dfyl)
        
        liftIO $ hSetBuffering stdout LineBuffering
        liftIO $ hSetBuffering stderr LineBuffering
        
        -- verify functional specification
        let func =        compileDafny False (debugVerification opts) dfyfile bplfile
              `seqStatus` axiomatizeBoogaman (debugVerification opts) axs bplfile bplfile2
              `seqStatus` runBoogie False (debugVerification opts) bplfile2
        
        -- verify leakage specification
        let spec =        compileDafny True (debugVerification opts) dfylfile bpllfile
              `seqStatus` shadowBoogaman (debugVerification opts) axsl bpllfile bpllfile2
              `seqStatus` runBoogie True (debugVerification opts) bpllfile2

        res <- lift $ case verify opts of
            FuncV -> func
            LeakV -> spec
            BothV -> do
                (fres,sres) <- concurrently func spec
                return $ mappend fres sres
        printStatus res

compileDafny :: (MonadIO m) => Bool -> Bool -> FilePath -> FilePath -> m Status
compileDafny isLeak isDebug dfy bpl = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Compiling Dafny file" <+> text (show dfy)
    res <- shellyOutput isDebug "dafny" ["/compile:0",dfy,"/print:"++bpl,"/noVerify"]
    verifOutput isLeak True res

verifOutput :: (MonadIO m) => Bool -> Bool -> Status -> m Status
verifOutput isLeak isDafny st@(Status (Right err)) = verifErr isDafny st
verifOutput isLeak isDafny st@(Status (Left output)) = do
    let ls = lines $ show output
    let w = last ls
    let errs = filter (List.isPrefixOf "Prover error:") $ init ls
    let tool = if isDafny then "Dafny" else "Boogie"
    let parser = do
        Parsec.string tool >> Parsec.space
        Parsec.string "program" >> Parsec.space
        Parsec.string "verifier" >> Parsec.space
        Parsec.string "finished" >> Parsec.space
        Parsec.string "with" >> Parsec.space
        verified <- Parsec.int
        Parsec.space
        Parsec.string "verified" >> Parsec.char ',' >> Parsec.space
        errors <- Parsec.int
        Parsec.space
        Parsec.string "errors"
        return (verified,errors)
    let e = Parsec.parse parser "output" w
    if (List.null errs)
        then case e of
            Left err -> verifErr isDafny st
            Right (oks,kos) -> do
                let c = if isLeak then "leakage" else "functional"
                let res = if isDafny then PP.empty else text "Verified" <+> int oks <+> text c <+> text "properties with" <+> int kos <+> text "errors."
                case kos of
                    0 -> return $ Status $ Left res
                    otherwise -> error $ show res
        else verifErr isDafny st

verifErr :: MonadIO m => Bool -> Status -> m Status
verifErr isDafny (Status res) = do
    let exec = if isDafny then "Dafny" else "Boogie"
    case res of
        Left output -> return $ Status $ Right $ GenericError noloc (text "Unexpected" <+> text exec <+> text "verification error: " <+> output) Nothing
        Right err -> return $ Status $ Right $ GenericError noloc (text "Unexpected" <+> text exec <+> text "verification error:") (Just err)

axiomatizeBoogaman :: (MonadIO m) => Bool -> [String] -> FilePath -> FilePath -> m Status
axiomatizeBoogaman isDebug axioms bpl1 bpl2 = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Axiomatizing boogie file" <+> text (show bpl1) <+> text "into" <+> text (show bpl2) 
    let addaxiom x = text "--axioms=" <> text (escape x)
    command isDebug $ show $ text "cabal exec -- boogaman" <+> text bpl1
        <+> text "--simplify"
        <+> text "--vcgen=dafny"
        <+> Pretty.sepBy space (map addaxiom axioms)
        <+> text ">" <+> text bpl2
    
shadowBoogaman :: (MonadIO m) => Bool -> [String] -> FilePath -> FilePath -> m Status
shadowBoogaman isDebug axioms bpl1 bpl2 = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Shadowing boogie file" <+> text (show bpl1) <+> text "into" <+> text (show bpl2) 
    let addaxiom x = text "--axioms=" <> text (escape x)
    command isDebug $ show $ text "cabal exec -- boogaman" <+> text bpl1
        <+> text "--simplify"
        <+> text "--vcgen=dafny"
--        <+> text "--filterleakage=true"
        <+> text "--shadow"
        <+> Pretty.sepBy space (map addaxiom $ axioms)
        <+> text ">" <+> text bpl2

runBoogie :: (MonadIO m) => Bool -> Bool -> FilePath -> m Status
runBoogie isLeak isDebug bpl = do
    when isDebug $ liftIO $ hPutStrLn stderr $ show $ text "Verifying Boogie file" <+> text (show bpl)
    let dotrace = if isDebug then ["/trace"] else []
    res <- shellyOutput isDebug "boogie" $ dotrace ++ ["/doModSetAnalysis",bpl]
    verifOutput isLeak False res

getEntryPoints :: [(TypedModuleFile,OutputType)] -> TcM IO [DafnyId]
getEntryPoints files = do
    opts <- askOpts
    ps <- case entryPoints opts of
        (List.null -> True) -> do
            let files' = map fst $ filter ((/=NoOutput) . snd) files
            liftM concat $ mapM entryPointsTypedModuleFile files'
        es -> liftM catMaybes $ mapM resolveEntryPoint es
    return ps

output :: Options -> [FilePath] -> [FilePath] -> [TypedModuleFile] -> IO [(TypedModuleFile,OutputType)] 
output opts secrecIns secrecOuts modules = do
    moduleso <- resolveOutput secrecIns secrecOuts modules
    forM_ moduleso $ \(mfile,o) -> case mfile of
        Left (time,ppargs,m,ml) -> case o of
            NoOutput -> do
                when (printOutput opts) $ hPutStrLn stderr $ "No output for module " ++ show (moduleFile m)
                return ()
            OutputFile f -> writeFile f $ show $ ppid ppargs $+$ ppid m
            OutputStdout -> when (printOutput opts) $ do
                putStrLn $ show (moduleFile m) ++ ":"
                putStrLn $ show $ ppid ppargs $+$ ppid m
        Right sci -> do
            when (printOutput opts) $ hPutStrLn stderr $ "No output for unchanged module " ++ show (sciFile sci)
            return ()
    return moduleso

type EntryPoints = (Bool,Set String)

pruneModuleFiles :: [ModuleFile] -> State EntryPoints [ModuleFile]
pruneModuleFiles [] = return []
pruneModuleFiles (m:ms) = do
    m' <- pruneModuleFile m
    ms' <- pruneModuleFiles ms
    return (m':ms')

addEntryPoints :: Set String -> EntryPoints -> EntryPoints
addEntryPoints (Set.null -> True) (b,xs) = (True,xs)
addEntryPoints es (b,xs) = (b,Set.union xs es)

addGEntryPoints :: Data (a Identifier Position) => a Identifier Position -> EntryPoints -> EntryPoints
addGEntryPoints x (b,xs) = (b,Set.union xs (gEntryPoints x))

pruneModuleFile :: ModuleFile -> State EntryPoints ModuleFile
pruneModuleFile (Right sci) = return $ Right sci
pruneModuleFile (Left (t,pargs,m,i)) = do
    State.modify $ addEntryPoints $ Set.fromList $ entryPoints $ ppOptions pargs
    m' <- pruneModule m
    return $ Left (t,pargs,m',i)
  where
    pruneModule :: Module Identifier Position -> State EntryPoints (Module Identifier Position)
    pruneModule (Module l mn p) = do
        p' <- pruneProgram p
        return $ Module l mn p'
    pruneProgram :: Program Identifier Position -> State EntryPoints (Program Identifier Position)
    pruneProgram (Program l is gs) = do
        gs' <- pruneGlobalDecls gs
        return $ Program l is gs'
    pruneGlobalDecls :: [GlobalDeclaration Identifier Position] -> State EntryPoints [GlobalDeclaration Identifier Position]
    pruneGlobalDecls [] = return []
    pruneGlobalDecls (g:gs) = do
        g' <- pruneGlobalDecl g
        gs' <- pruneGlobalDecls gs
        return $ maybeToList g' ++ gs'
    pruneGlobalDecl :: GlobalDeclaration Identifier Position -> State EntryPoints (Maybe (GlobalDeclaration Identifier Position))
    pruneGlobalDecl d@(GlobalProcedure l p) = pruneName (procedureDeclarationName p) d
    pruneGlobalDecl d@(GlobalStructure l p) = pruneName (structureDeclarationName p) d
    pruneGlobalDecl d@(GlobalFunction l p) = pruneName (functionDeclarationName p) d
    pruneGlobalDecl d@(GlobalTemplate l p) = pruneName (templateDeclarationName p) d
    pruneGlobalDecl (GlobalAnnotations l as) = do
        as' <- pruneGlobalAnns as
        return $ Just $ GlobalAnnotations l as'
    pruneGlobalDecl d = do
        State.modify $ addGEntryPoints d
        return $ Just d
    pruneGlobalAnns :: [GlobalAnnotation Identifier Position] -> State EntryPoints [GlobalAnnotation Identifier Position]
    pruneGlobalAnns [] = return []
    pruneGlobalAnns (a:as) = do
        a' <- pruneGlobalAnn a
        as' <- pruneGlobalAnns as
        return $ maybeToList a' ++ as'
    pruneGlobalAnn :: GlobalAnnotation Identifier Position -> State EntryPoints (Maybe (GlobalAnnotation Identifier Position))
    pruneGlobalAnn a = case globalAnnName a of
        Nothing -> do
            State.modify $ addGEntryPoints a
            return $ Just a
        Just n -> pruneName n a
    pruneName :: Data (a Identifier Position) => Identifier -> a Identifier Position -> State EntryPoints (Maybe (a Identifier Position))
    pruneName n d = do
        (b,es) <- State.get
        case b of
            True -> trace ("all did not prune " ++ show n ++ " in " ++ show es) $ do
                State.modify $ addGEntryPoints d
                return $ Just d
            False -> if List.elem n es
                then trace ("did not prune " ++ show n ++ " in " ++ show es) $ do
                    State.modify $ addGEntryPoints d
                    return (Just d)
                else trace ("pruned " ++ show n ++ " in " ++ show es) $ do
                    return Nothing

gEntryPoints :: Data (a Identifier Position) => a Identifier Position -> Set String
gEntryPoints x = everything (Set.union) (mkQ Set.empty auxP `extQ` auxO `extQ` auxS) x
    where
    auxP :: ProcedureName Identifier Position -> Set String
    auxP pn = Set.singleton $ procedureNameId pn
    auxO :: Op Identifier Position -> Set String
    auxO o = Set.singleton $ pprid o
    auxS :: TypeName Identifier Position -> Set String
    auxS s = Set.singleton $ typeId s

secrec :: Options -> IO ()
secrec opts = do
    let secrecIns = inputs opts
    let secrecOuts = outputs opts
    when (List.null secrecIns) $ throwError $ userError "no SecreC input files"
    runSecrecM opts $ do
        modules <- parseModuleFiles secrecIns
        let es = case entryPoints opts of
                    [] -> (True,Set.empty)
                    es -> (False,Set.fromList es)
        let modules' = reverse $ State.evalState (pruneModuleFiles (reverse modules)) es
        passes secrecIns secrecOuts modules'
        

