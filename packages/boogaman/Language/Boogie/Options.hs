{-# LANGUAGE DeriveDataTypeable #-}

module Language.Boogie.Options where

import Data.Typeable
import Data.Generics

import Language.Boogie.AST

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
        }
    deriving (Show, Data, Typeable)