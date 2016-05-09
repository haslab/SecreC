{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Conversion where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Prover.Base
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Error

import Control.Monad.Except

type ConversionK loc m = (Location loc,MonadError SecrecError m)

type2TypeSpecifierNonVoid :: ConversionK loc m => loc -> Type -> m ((TypeSpecifier VarIdentifier (Typed loc)))