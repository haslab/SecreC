module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars

import Data.Int
import Data.Word

typeToSecType :: (Vars loc,Location loc) => loc -> Type -> TcM loc SecType
typeToBaseType :: (Vars loc,Location loc) => loc -> Type -> TcM loc BaseType
typeToComplexType :: (Vars loc,Location loc) => loc -> Type -> TcM loc ComplexType
typeToDecType :: (Vars loc,Location loc) => loc -> Type -> TcM loc DecType

tcTypeSpec :: (Vars loc,Location loc) => TypeSpecifier Identifier loc -> TcM loc (TypeSpecifier VarIdentifier (Typed loc))

tcSecTypeSpec :: (Vars loc,Location loc) => SecTypeSpecifier Identifier loc -> TcM loc (SecTypeSpecifier VarIdentifier (Typed loc))

tcRetTypeSpec :: (Vars loc,Location loc) => ReturnTypeSpecifier Identifier loc -> TcM loc (ReturnTypeSpecifier VarIdentifier (Typed loc))

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))

typeDim :: (Vars loc,Location loc) => loc -> ComplexType -> TcM loc (Maybe Word64)

projectMatrixType :: (Vars loc,Location loc) => loc -> ComplexType -> [ArrayProj] -> TcM loc ComplexType

projectStructField :: (Vars loc,Location loc) => loc -> DecType -> AttributeName VarIdentifier () -> TcM loc Type

refineTypeSizes :: (Vars loc,Location loc) => loc -> ComplexType -> Maybe (Sizes VarIdentifier Type) -> TcM loc ComplexType
