module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base

tcTypeSpec :: Location loc => TypeSpecifier loc -> TcM loc (TypeSpecifier (Typed loc))

tcRetTypeSpec :: Location loc => ReturnTypeSpecifier loc -> TcM loc (ReturnTypeSpecifier (Typed loc))

typeDim :: Location loc => loc -> Type -> TcReaderM loc Int