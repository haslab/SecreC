module Language.SecreC.TypeChecker.Statement where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.TypeChecker.Base

tcStmt :: (Vars loc,Location loc) => Type -> Statement Identifier loc -> TcM loc (Statement VarIdentifier (Typed loc),Type)