{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}

module Main where

import qualified Data.List as List
import Data.List.Split
import Data.Version (showVersion)

import Language.SecreC.Pretty as Pretty
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Modules
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker
import Language.SecreC.Monad
import Language.SecreC.Utils

import System.Console.CmdArgs
import System.Environment
import System.FilePath

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Except

import Text.PrettyPrint hiding (mode,Mode(..))

import Paths_SecreC


--getDataFileName :: String -> IO String
--getDataFileName p = return $ ".." </> p

-- * main function

main :: IO ()
main = do
    opts <- getOpts
    case opts of
        Opts  {} -> secrec opts

-- * front-end options

opts  :: Options
opts  = Opts { 
      inputs                = inputs defaultOptions &= args &= typ "FILE.sc"
    , outputs               = outputs defaultOptions &= typ "FILE1.sc:...:FILE2.sc" &= help "Output SecreC files"
    , paths                 = paths defaultOptions &= typ "DIR1:...:DIRn" &= help "Import paths for input SecreC program"
    , parser                = parser defaultOptions &= typ "parsec OR derp" &= help "backend Parser type"
    , implicitBuiltin       = implicitBuiltin defaultOptions &= name "builtin" &= help "Implicitly import the builtin module"
    
    -- Optimization
    , knowledgeInference    = knowledgeInference defaultOptions &= name "ki" &= help "Infer private data from public data" &= groupname "Optimization"
    
    -- Verification
    , typeCheck             = typeCheck defaultOptions &= name "tc" &= help "Typecheck the SecreC input" &= groupname "Verification"

    -- Debugging
    , debugLexer            = debugLexer defaultOptions &= name "debug-lexer" &= explicit &= help "Print lexer tokens to stderr" &= groupname "Debugging"
    , debugParser           = debugParser defaultOptions &= name "debug-parser" &= explicit &= help "Print parser result to stderr" &= groupname "Debugging"
    , debugTypechecker           = debugTypechecker defaultOptions &= name "debug-typechecker" &= explicit &= help "Print typechecker result to stderr" &= groupname "Debugging"
    
    -- Typechecker
    , implicitClassify   = implicitClassify defaultOptions &= name "implicit" &= help "Enables implicit classification of public data" &= groupname "Verification:Typechecker"
    , externalSMT   = externalSMT defaultOptions &= name "smt" &= help "Use an external SMT solver for index constraints" &= groupname "Verification:Typechecker"
    , constraintStackSize   = constraintStackSize defaultOptions &= name "k-stack-size" &= help "Sets the constraint stack size for the typechecker" &= groupname "Verification:Typechecker"
    , evalTimeOut           = evalTimeOut defaultOptions &= name "eval-timeout" &= explicit &= help "Timeout for evaluation expression in the typechecking phase" &= groupname "Verification:Typechecker"
    }
    &= help "SecreC analyser"

mode  :: Mode (CmdArgs Options)
mode  = cmdArgsMode $
           modes [opts &= auto]
        &= help "SecreC analyser"
        &= summary ("secrec " ++ showVersion version ++ " \n\
                   \(C) PRACTICE TEAM 2015 - DI/HasLab - Univ. Minho,\
                   \ Braga, Portugal")

printHelp :: IO ()
printHelp = withArgs ["--help"] $ cmdArgsRun mode >> return ()

getOpts :: IO Options
getOpts = getArgs >>= doGetOpts
    where 
    doGetOpts as
        | null as   = withArgs ["--help"] $ cmdArgsRun mode >>= processOpts
        | otherwise = cmdArgsRun mode >>= processOpts

processOpts :: Options -> IO Options
processOpts opts = do
    p1 <- getDataFileName "imports"
    p2 <- getDataFileName ("imports" </> "stdlib" </> "lib")
    return $ opts
        { outputs = parsePaths $ outputs opts
        , paths = parsePaths $ p1 : p2 : paths opts
        , typeCheck = typeCheck opts || knowledgeInference opts
        }

parsePaths :: [FilePath] -> [FilePath]
parsePaths = concatMap (splitOn ":")

-- back-end code

data OutputType = OutputFile FilePath | OutputStdout | NoOutput
  deriving (Show,Read,Data,Typeable)

defaultOutputType = NoOutput

-- | Set output mode for processed modules:
-- * inputs with explicit output files write to the file
-- * inputs without explicit output files write to stdout
-- * non-input modules do not output
resolveOutput :: [FilePath] -> [FilePath] -> [Module Identifier Position] -> [(Module Identifier Position,OutputType)]
resolveOutput inputs outputs modules = map res modules
    where
    db = zipLeft inputs outputs
    res m = case List.lookup (moduleFile m) db of
        Just (Just o) -> (m,OutputFile o) -- input with matching output
        Just Nothing -> (m,OutputStdout) -- intput without matching output
        Nothing -> (m,NoOutput) -- non-input loaded module

secrec :: Options -> IO ()
secrec opts = do
    let secrecFiles = inputs opts
    let secrecOuts = outputs opts
    when (List.null secrecFiles) $ throwError $ userError "no SecreC input files"
    runSecrecM opts $ do
        modules <- parseModuleFiles secrecFiles
        let moduleso = resolveOutput secrecFiles secrecOuts modules
        let printMsg str = liftIO $ putStrLn $ show $ text "Modules" <+> Pretty.sepBy (char ',') (map (text . modulePosId) modules) <+> text str <> char '.'
        if (typeCheck opts)
            then runTcM $ do
                typedModulesO <- fmapFstM tcModule moduleso
                printMsg "are well-typed"
            else printMsg "parsed OK"
        

