{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.Prover.Base

import Data.Int
import Data.Word

import Control.Monad.IO.Class

castTypeToType :: CastType VarIdentifier Type -> Type

isBoolTypeM :: (ProverK loc m) => loc -> Type -> TcM m Bool
isIntTypeM :: (ProverK loc m) => loc -> Type -> TcM m Bool

typeToSecType :: (ProverK loc m) => loc -> Type -> TcM m SecType
typeToBaseType :: (ProverK loc m) => loc -> Type -> TcM m BaseType
typeToComplexType :: (ProverK loc m) => loc -> Type -> TcM m ComplexType
typeToDecType :: (ProverK loc m) => loc -> Type -> TcM m DecType
typeToVArrayType :: (ProverK loc m) => loc -> Type -> SExpr VarIdentifier Type -> TcM m VArrayType

typeSize :: (ProverK loc m) => loc -> Type -> TcM m (SExpr VarIdentifier Type)

tcTypeSpec :: (ProverK loc m) => TypeSpecifier Identifier loc -> IsVariadic -> TcM m (TypeSpecifier VarIdentifier (Typed loc))

tcSecType :: (ProverK loc m) => SecTypeSpecifier Identifier loc -> TcM m (SecTypeSpecifier VarIdentifier (Typed loc))

tcRetTypeSpec :: (ProverK loc m) => ReturnTypeSpecifier Identifier loc -> TcM m (ReturnTypeSpecifier VarIdentifier (Typed loc))

tcPrimitiveDatatype :: (MonadIO m,Location loc) => PrimitiveDatatype loc -> TcM m (PrimitiveDatatype (Typed loc))

typeDim :: (ProverK loc m) => loc -> Type -> TcM m (SExpr VarIdentifier Type)

matchTypeDimension :: (ProverK loc m) => loc -> SExpr VarIdentifier Type -> [(SExpr VarIdentifier Type,IsVariadic)] -> TcM m ()

projectMatrixType :: (ProverK loc m) => loc -> Type -> [ArrayProj] -> TcM m Type

projectStructField :: (ProverK loc m) => loc -> BaseType -> AttributeName VarIdentifier () -> TcM m Type

refineTypeSizes :: (ProverK loc m) => loc -> Type -> Maybe (Sizes VarIdentifier Type) -> TcM m Type
tcCastType :: (MonadIO m,Location loc) => CastType Identifier loc -> TcM m (CastType VarIdentifier (Typed loc))

tcTemplateTypeArgument :: (ProverK loc m) => TemplateTypeArgument Identifier loc -> TcM m (TemplateTypeArgument VarIdentifier (Typed loc))

tcTypeSizes :: (ProverK loc m) => loc -> Type -> Maybe (Sizes Identifier loc) -> TcM m (Type,Maybe (Sizes VarIdentifier (Typed loc)))

typeToPrimType :: (ProverK loc m) => loc -> Type -> TcM m Prim

typeBase :: (ProverK loc m) => loc -> Type -> TcM m Type