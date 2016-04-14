{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Data.Version (showVersion)

import System.Console.CmdArgs hiding (program)
import System.IO
import System.Environment

import Text.ParserCombinators.Parsec (parse, parseFromFile)
import Text.PrettyPrint.ANSI.Leijen

import Language.Boogie.Parser
import Language.Boogie.Transformation
import Language.Boogie.PrettyAST

import Paths_Boogaman

main :: IO ()
main = do
    opts <- getOpts
    case opts of
        Opts  {} -> boogaman opts

-- * front-end options

printHelp :: IO ()
printHelp = withArgs ["--help"] $ cmdArgsRun mode >> return ()

mode  :: Mode (CmdArgs Options)
mode  = cmdArgsMode $
           modes [opts &= auto]
        &= help "Boogie AST Manipulator"
        &= summary ("boogaman " ++ showVersion version ++ " \n\
                   \(C) PRACTICE TEAM 2016 - DI/HasLab - Univ. Minho,\
                   \ Braga, Portugal")

getOpts :: IO Options
getOpts = getArgs >>= doGetOpts
    where 
    doGetOpts as
        | null as   = withArgs ["--help"] $ cmdArgsRun mode
        | otherwise = cmdArgsRun mode

defaultOptions :: Options
defaultOptions = Opts
    { input = []
    , output = []
    , shadow = False
    , simplify = False
    , leakage = Nothing
    , vcgen = NoVCGen
    , axioms = []
    }

opts  :: Options
opts  = Opts { 
      input                = input defaultOptions &= args &= typ "FILE.bpl"
    , output               = output defaultOptions &= typ "FILE.bpl:" &= help "Output Boogie file"
    , shadow            = shadow defaultOptions &= help "Shadow the original program" &= groupname "Transformation"
    , simplify            = simplify defaultOptions &= help "Simplify boogie code" &= groupname "Transformation"
    , leakage         = leakage defaultOptions &= help "Consider or discard leakage annotations" &= groupname "Transformation"
    , vcgen           = vcgen defaultOptions &= help "Specializes the transformations for the given VCGen"
    , axioms          = axioms defaultOptions &= help "axiomatize contracts of given procedures"
    }
    &= help "Boogie AST Manipulator analyser"

boogaman :: Options -> IO ()
boogaman opts = do
    parseResult <- parseFromFile program (input opts)
    case parseResult of
            Left err -> hPutStrLn stderr $ show err
            Right input -> do
                output <- transform opts input
                putStrLn $ show $ pretty output



