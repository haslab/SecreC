module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars

tcTypeSpec :: Location loc => TypeSpecifier loc -> TcM loc (TypeSpecifier (Typed loc))

tcSecTypeSpec :: Location loc => SecTypeSpecifier loc -> TcReaderM loc (SecTypeSpecifier (Typed loc))

tcRetTypeSpec :: Location loc => ReturnTypeSpecifier loc -> TcM loc (ReturnTypeSpecifier (Typed loc))

typeDim :: Location loc => loc -> Type -> TcM loc (Maybe Integer)

matchTemplateType :: Location loc => loc -> TIdentifier -> [Type] -> TcReaderM loc [EntryEnv loc] -> TDict -> TcM loc (Type,Position,TDict)

projectStructField :: Location loc => loc -> Type -> AttributeName loc -> TcM loc Type

projectMatrixType :: Location loc => loc -> Type -> [(Maybe Integer,Maybe Integer)] -> TcM loc Type