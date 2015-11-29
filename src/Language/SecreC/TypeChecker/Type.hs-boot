module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars

import Data.Int
import Data.Word

tcTypeSpec :: (Vars loc,Location loc) => TypeSpecifier Identifier loc -> TcM loc (TypeSpecifier VarIdentifier (Typed loc))

tcSecTypeSpec :: Location loc => SecTypeSpecifier Identifier loc -> TcM loc (SecTypeSpecifier VarIdentifier (Typed loc))

tcRetTypeSpec :: (Vars loc,Location loc) => ReturnTypeSpecifier Identifier loc -> TcM loc (ReturnTypeSpecifier VarIdentifier (Typed loc))

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))

typeDim :: (Vars loc,Location loc) => loc -> Type -> TcM loc (Maybe Word64)

projectMatrixType :: (Vars loc,Location loc) => loc -> Type -> [ArrayProj] -> TcM loc Type

projectStructField :: (Vars loc,Location loc) => loc -> Type -> AttributeName VarIdentifier () -> TcM loc Type

refineTypeSizes :: (Vars loc,Location loc) => loc -> Type -> Maybe (Sizes VarIdentifier Type) -> TcM loc Type
