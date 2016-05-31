{-# LANGUAGE DeriveDataTypeable #-}
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

import System.Console.CmdArgs
import System.Environment
import System.FilePath

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

-- back-end code

data OutputType = OutputFile FilePath | OutputStdout | NoOutput
  deriving (Show,Read,Data,Typeable)

defaultOutputType = NoOutput

-- | Set output mode for processed modules:
-- * inputs with explicit output files write to the file
-- * inputs without explicit output files write to stdout
-- * non-input modules do not output
resolveOutput :: [FilePath] -> [FilePath] -> [ModuleFile] -> [(ModuleFile,OutputType)]
resolveOutput inputs outputs modules = map res modules
    where
    db = zipLeft inputs outputs
    res (Left (time,ppargs,m)) = case List.lookup (moduleFile m) db of
        Just (Just o) -> (Left (time,ppargs,m),OutputFile o) -- input with matching output
        Just Nothing -> (Left (time,ppargs,m),OutputStdout) -- intput without matching output
        Nothing -> (Left (time,ppargs,m),NoOutput) -- non-input loaded module
    res (Right sci) = (Right sci,NoOutput)

passes :: [(ModuleFile,OutputType)] -> SecrecM IO ()
passes modules = runTcM $ failTcM (noloc::Position) $ localOptsTcM (\opts -> opts { failTypechecker = False }) $ do
    tc <- typecheck modules
    case tc of
        Nothing -> return ()
        Just typedModules -> do
            opts <- askOpts
            simpleModules <- fmapFstM (simplifyModuleFile opts) typedModules
            liftIO $ output simpleModules

typecheck :: [(ModuleFile,OutputType)] -> TcM IO (Maybe [(TypedModuleFile,OutputType)])
typecheck modules = do
    opts <- askOpts
    let printMsg str = liftIO $ putStrLn $ show $ text "Modules" <+> Pretty.sepBy (char ',') (map (text . moduleId . thr3) $ lefts $ map fst modules) <+> text str <> char '.'
    if (typeCheck opts)
        then do
            typedModules <- fmapFstM tcModuleFile modules
            printMsg "are well-typed"
            return $ Just typedModules
        else do
            printMsg "parsed OK" 
            return Nothing

output :: [(TypedModuleFile,OutputType)] -> IO () 
output modules = forM_ modules $ \(mfile,o) -> case mfile of
    Left (time,ppargs,m) -> case o of
        NoOutput -> return ()
        OutputFile f -> writeFile f $ show $ pp ppargs $+$ pp m
        OutputStdout -> do
            putStrLn $ show (moduleFile m) ++ ":"
            putStrLn $ show $ pp ppargs $+$ pp m
    Right sci -> return ()

secrec :: Options -> IO ()
secrec opts = do
    let secrecFiles = inputs opts
    let secrecOuts = outputs opts
    when (List.null secrecFiles) $ throwError $ userError "no SecreC input files"
    runSecrecM opts $ do
        modules <- parseModuleFiles secrecFiles
        let moduleso = resolveOutput secrecFiles secrecOuts modules
        passes moduleso
        

