module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars

matchTemplate :: (Vars loc,Location loc) => loc -> TIdentifier -> [Type] -> Maybe Type -> TcM loc [EntryEnv loc] -> TcM loc (Type,Type)