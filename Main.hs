{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}

module Main where

import qualified Data.List as List
import Data.List.Split

import Language.SecreC.Parser.Parser
import Language.SecreC.Pretty
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Modules
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Monad

import System.Console.CmdArgs
import System.Environment

import Control.Monad
import Control.Monad.IO.Class

-- * main function

main :: IO ()
main = do
    opts <- getOpts
    case opts of
        Help     -> printHelp
        Opts  {} -> secrec opts

-- * front-end options

data Options
    = Opts  { 
          inputs                :: [FilePath]
        , output                :: Maybe FilePath
        , paths                 :: [FilePath]
        , knowledgeInference    :: Bool
        , typeCheck             :: Bool
        }
    | Help
    deriving (Show, Data, Typeable)

opts  :: Options
opts  = Opts { 
      inputs                = def &= args &= typ "FILE.sc"
    , output                = def &= typ "FILE.sc" &= help "Output SecreC file"
    , paths                 = def &= typ "DIR1:...:DIRn" &= help "Import paths for input SecreC program"
    , knowledgeInference    = def &= name "ki" &= help "Infer private data from public data" &= groupname "Optimization"
    , typeCheck             = True &= name "tc" &= help "Typecheck the SecreC input" &= groupname "Verification"
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
        | otherwise = liftM processOpts $ cmdArgsRun mode

processOpts :: Options -> Options
processOpts opts = Opts
    (inputs opts)
    (output opts)
    (parsePaths (paths opts))
    (knowledgeInference opts)
    (typeCheck opts || knowledgeInference opts)

parsePaths :: [FilePath] -> [FilePath]
parsePaths = concatMap (splitOn ":")

-- back-end code

secrec :: Options -> IO ()
secrec opts = do
    let secrecFiles = inputs opts
    when (List.null secrecFiles) $ error "no SecreC input files"
    ioSecrecM $ do
        modules <- parseModuleFiles (paths opts) secrecFiles
        when (typeCheck opts) $ runTcM $ forM_ modules $ \ast -> do
            -- TODO: make this actually do something!
            liftIO $ secreCOutput opts ast

secreCOutput :: Options -> Module loc -> IO ()
secreCOutput opts ast = case output opts of
    Nothing -> putStrLn (ppr ast)
    Just output -> writeFile output (ppr ast)
    