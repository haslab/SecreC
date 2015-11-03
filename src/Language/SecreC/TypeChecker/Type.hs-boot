module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars

tcTypeSpec :: Location loc => TypeSpecifier loc -> TcM loc (TypeSpecifier (Typed loc))

tcSecTypeSpec :: Location loc => SecTypeSpecifier loc -> TcReaderM loc (SecTypeSpecifier (Typed loc))

tcRetTypeSpec :: Location loc => ReturnTypeSpecifier loc -> TcM loc (ReturnTypeSpecifier (Typed loc))

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))

typeDim :: Location loc => loc -> Type -> TcM loc (Maybe Integer)

projectMatrixType :: Location loc => loc -> Type -> [(Maybe Integer,Maybe Integer)] -> TcProofM loc Type

projectStructField :: Location loc => loc -> Type -> AttributeName () -> TcProofM loc Type

castType :: Location loc => loc -> Type -> Type -> TcProofM loc Type