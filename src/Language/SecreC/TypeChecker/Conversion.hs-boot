{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Conversion where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Prover.Base
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Pretty

import Data.Typeable
import Control.Monad.Except

type ConversionK loc m = ProverK loc m

type2TypeSpecifierNonVoid :: ConversionK loc m => loc -> Type -> TcM m ((TypeSpecifier GIdentifier (Typed loc)))

baseType2DatatypeSpecifier :: ConversionK loc m => loc -> BaseType -> TcM m (DatatypeSpecifier GIdentifier (Typed loc))

type2TypeSpecifier :: ConversionK loc m => loc -> Type -> TcM m (Maybe (TypeSpecifier GIdentifier (Typed loc)))

secType2SecTypeSpecifier :: ConversionK loc m => loc -> SecType -> TcM m (SecTypeSpecifier GIdentifier (Typed loc))

type2TemplateTypeArgument :: ConversionK loc m => loc -> Type -> TcM m (TemplateTypeArgument GIdentifier (Typed loc))