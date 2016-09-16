{-# LANGUAGE DeriveDataTypeable #-}

module Language.Boogie.Options where

import Data.Typeable
import Data.Generics

import Language.Boogie.AST

import System.IO

import Control.Monad.State

data VCGen
    = NoVCGen
    | Dafny
  deriving (Show, Data, Typeable,Eq)

data Options
    = Opts  { 
          input                :: FilePath
        , output               :: FilePath
        , shadow               :: Bool
        , simplify             :: Bool
        , filterLeakage        :: Maybe Bool
        , vcgen                :: VCGen
        , axioms               :: [Id]
        , debug                :: Bool
        }
    deriving (Show, Data, Typeable)
    
strace :: MonadIO m => Options -> String -> m a -> m a
strace opts str m = do
    when (debug opts) $ liftIO $ hPutStrLn stderr str
    m