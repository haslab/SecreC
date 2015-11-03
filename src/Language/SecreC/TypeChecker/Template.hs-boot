module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax

type TIdentifier = Either Identifier Identifier

matchTemplate :: Location loc => loc -> TIdentifier -> [Type] -> Maybe Type -> TcReaderM loc [EntryEnv loc] -> TcM loc (Type,Type)