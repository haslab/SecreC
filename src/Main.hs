{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}

module Main where

import qualified Data.List as List
import Data.List.Split

import Language.SecreC.Pretty as Pretty
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Modules
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker
import Language.SecreC.Monad
import Language.SecreC.Utils

import System.Console.CmdArgs
import System.Environment
import System.FilePath

import Control.Monad
import Control.Monad.IO.Class

import Text.PrettyPrint hiding (mode,Mode(..))

import Paths_SecreC

-- * main function

main :: IO ()
main = do
    opts <- getOpts
    case opts of
        Help     -> printHelp
        Opts  {} -> secrec opts

-- * front-end options

opts  :: Options
opts  = Opts { 
      inputs                = def &= args &= typ "FILE.sc"
    , outputs               = def &= typ "FILE1.sc:...:FILE2.sc" &= help "Output SecreC files"
    , paths                 = def &= typ "DIR1:...:DIRn" &= help "Import paths for input SecreC program"
    , parser                = Parsec &= typ "parsec OR derp" &= help "backend Parser type"
    , knowledgeInference    = def &= name "ki" &= help "Infer private data from public data" &= groupname "Optimization"
    , typeCheck             = True &= name "tc" &= help "Typecheck the SecreC input" &= groupname "Verification"
    , debugLexer            = def &= name "debug-lexer" &= explicit &= help "Print lexer tokens to stderr" &= groupname "Debugging"
    , debugParser            = def &= name "debug-parser" &= explicit &= help "Print parser result to stderr" &= groupname "Debugging"
    }
    &= help "SecreC analyser"

chelp :: Options
chelp = Help
     &= help "Display help about SecreC modes"

mode  :: Mode (CmdArgs Options)
mode  = cmdArgsMode $
           modes [opts &= auto, chelp]
        &= help "SecreC analyser"
        &= summary "secrec v0.1 \n\
                   \(C) PRACTICE TEAM 2015 - DI/HasLab - Univ. Minho,\
                   \ Braga, Portugal"

printHelp :: IO ()
printHelp = withArgs ["--help"] $ cmdArgsRun mode >> return ()

getOpts :: IO Options
getOpts = getArgs >>= doGetOpts
    where 
    doGetOpts as
        | null as   = withArgs ["help"] $ cmdArgsRun mode
        | otherwise = cmdArgsRun mode >>= processOpts

processOpts :: Options -> IO Options
processOpts opts = do
    p1 <- getDataFileName "imports"
    p2 <- getDataFileName ("imports" </> "stdlib" </> "lib")
    return $ Opts
        (inputs opts)
        (parsePaths $ outputs opts)
        (parsePaths $ p1 : p2 : paths opts)
        (parser opts)
        (knowledgeInference opts)
        (typeCheck opts || knowledgeInference opts)
        (debugLexer opts)
        (debugParser opts)

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
    when (List.null secrecFiles) $ error "no SecreC input files"
    ioSecrecM opts $ do
        modules <- parseModuleFiles secrecFiles
        let moduleso = resolveOutput secrecFiles secrecOuts modules
        let printMsg str = liftIO $ putStrLn $ show $ text "Modules" <+> Pretty.sepBy (char ',') (map (text . modulePosId) modules) <+> text str <> char '.'
        if (typeCheck opts)
            then runTcM $ do
                typedModulesO <- mapFstM tcModule moduleso
                printMsg "are well-typed"
            else printMsg "parsed OK"
        

