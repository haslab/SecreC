{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars

import Data.Int
import Data.Word

import Control.Monad.IO.Class

castTypeToType :: CastType VarIdentifier Type -> Type

isBoolTypeM :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Bool
isIntTypeM :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Bool

typeToSecType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m SecType
typeToBaseType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m BaseType
typeToComplexType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m ComplexType
typeToDecType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m DecType

tcTypeSpec :: (VarsIdTcM loc m,Location loc) => TypeSpecifier Identifier loc -> TcM loc m (TypeSpecifier VarIdentifier (Typed loc))

tcSecTypeSpec :: (VarsIdTcM loc m,Location loc) => SecTypeSpecifier Identifier loc -> TcM loc m (SecTypeSpecifier VarIdentifier (Typed loc))

tcRetTypeSpec :: (VarsIdTcM loc m,Location loc) => ReturnTypeSpecifier Identifier loc -> TcM loc m (ReturnTypeSpecifier VarIdentifier (Typed loc))

tcPrimitiveDatatype :: (MonadIO m,Location loc) => PrimitiveDatatype loc -> TcM loc m (PrimitiveDatatype (Typed loc))

typeDim :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> TcM loc m (SExpr VarIdentifier Type)

matchTypeDimension :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Word64 -> TcM loc m ()

projectMatrixType :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> [ArrayProj] -> TcM loc m ComplexType

projectStructField :: (VarsIdTcM loc m,Location loc) => loc -> BaseType -> AttributeName VarIdentifier () -> TcM loc m Type

refineTypeSizes :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Maybe (Sizes VarIdentifier Type) -> TcM loc m ComplexType

tcCastType :: (MonadIO m,Location loc) => CastType Identifier loc -> TcM loc m (CastType VarIdentifier (Typed loc))

tcTemplateTypeArgument :: (VarsIdTcM loc m,Location loc) => TemplateTypeArgument Identifier loc -> TcM loc m (TemplateTypeArgument VarIdentifier (Typed loc))

tcTypeSizes :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Maybe (VarName Identifier loc) -> Maybe (Sizes Identifier loc) -> TcM loc m (ComplexType,Maybe (Sizes VarIdentifier (Typed loc)))

checkIndex :: (VarsIdTcM loc m,Location loc) => loc -> SExpr VarIdentifier Type -> TcM loc m ()

checkArrayAccess :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Word64 -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()

typeToPrimType :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Prim