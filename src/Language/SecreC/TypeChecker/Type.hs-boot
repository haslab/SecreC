{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars

import Data.Int
import Data.Word

typeToSecType :: (VarsTcM loc,Location loc) => loc -> Type -> TcM loc SecType
typeToBaseType :: (VarsTcM loc,Location loc) => loc -> Type -> TcM loc BaseType
typeToComplexType :: (VarsTcM loc,Location loc) => loc -> Type -> TcM loc ComplexType
typeToDecType :: (VarsTcM loc,Location loc) => loc -> Type -> TcM loc DecType

tcTypeSpec :: (VarsTcM loc,Location loc) => TypeSpecifier Identifier loc -> TcM loc (TypeSpecifier VarIdentifier (Typed loc))

tcSecTypeSpec :: (VarsTcM loc,Location loc) => SecTypeSpecifier Identifier loc -> TcM loc (SecTypeSpecifier VarIdentifier (Typed loc))

tcRetTypeSpec :: (VarsTcM loc,Location loc) => ReturnTypeSpecifier Identifier loc -> TcM loc (ReturnTypeSpecifier VarIdentifier (Typed loc))

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))

typeDim :: (VarsTcM loc,Location loc) => loc -> ComplexType -> TcM loc (Maybe Word64)

projectMatrixType :: (VarsTcM loc,Location loc) => loc -> ComplexType -> [ArrayProj] -> TcM loc ComplexType

projectStructField :: (VarsTcM loc,Location loc) => loc -> BaseType -> AttributeName VarIdentifier () -> TcM loc Type

refineTypeSizes :: (VarsTcM loc,Location loc) => loc -> ComplexType -> Maybe (Sizes VarIdentifier Type) -> TcM loc ComplexType

tcCastType :: Location loc => CastType Identifier loc -> TcM loc (CastType VarIdentifier (Typed loc))