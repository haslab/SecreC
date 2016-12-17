{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.IO where

import System.Console.CmdArgs
import System.Environment
import System.FilePath
import System.IO
import System.Posix.Escape
import System.Process
import System.Exit

import qualified Data.List as List
import Data.List.Split
import Data.Either
import Data.Version (showVersion)
import Data.Maybe
import qualified Data.Text as Text

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Except

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Pretty as Pretty
import Language.SecreC.Position
import Language.SecreC.Location

import Text.PrettyPrint hiding (mode,Mode(..))
import qualified Text.PrettyPrint as PP
import Text.Read
import qualified Data.Text.IO as Text

import qualified Shelly as Shelly

seqStatus :: Monad m => m Status -> m Status -> m Status
seqStatus mx my = do
    sx <- mx
    case unStatus sx of
        Left dx -> liftM (mappend sx) my
        Right err -> return sx

newtype Status = Status { unStatus :: Either Doc SecrecError }

instance Monoid Status where
    mempty = Status $ Left PP.empty
    mappend (Status (Left d1)) (Status (Left d2)) = Status $ Left $ d1 $+$ d2
    mappend (Status (Right err)) _ = Status $ Right err
    mappend _ (Status (Right err)) = Status $ Right err

statusOk :: Status
statusOk = mempty

printStatus :: (MonadIO m,MonadError SecrecError m) => Status -> m ()
printStatus (Status (Left d)) = liftIO $ putStrLn $ show d
printStatus (Status (Right err)) = throwError err

command :: (MonadIO m) => Bool -> String -> m Status
command doDebug cmd = do
    when doDebug $ liftIO $ hPutStrLn stderr $ "Running command " ++ show cmd
    exit <- liftIO $ system cmd
    case exit of
        ExitSuccess -> return statusOk
        ExitFailure err -> return $ Status $ Right $ GenericError noloc (int err) Nothing

commandOutput :: (MonadIO m) => Bool -> String -> m Status
commandOutput doDebug str = do
    when doDebug $ liftIO $ hPutStrLn stderr $ "Running command " ++ show str
    let process = (shell str) { std_out = CreatePipe }
    (_,Just hout,_,ph) <- liftIO $ createProcess process
    exit <- liftIO $ waitForProcess ph
    result <- liftIO $ hGetContents hout
    case exit of
        ExitSuccess -> return $ Status $ Left $ text result
        ExitFailure code -> return $ Status $ Right $ GenericError noloc (text "Error running command:" <+> int code $+$ text result) Nothing

shellyOutput :: (MonadIO m) => Bool -> Bool -> String -> [String] -> m Status
shellyOutput doDebug doSilent name args = do
    let silence = if doSilent then Shelly.silently else id
    when doDebug $ liftIO $ hPutStrLn stderr $ "Running command " ++ show (name ++ " " ++ unwords args)
    liftIO $ Shelly.shelly $ do
        result <- Shelly.errExit False $ silence $ Shelly.run (Shelly.fromText $ Text.pack name) (map Text.pack args)
        let uresult = Text.unpack result
        exit <- Shelly.lastExitCode
        case exit of
            0 -> return $ Status $ Left $ text uresult
            code -> return $ Status $ Right $ GenericError noloc (text "Error running command:" <+> int code $+$ text uresult) Nothing