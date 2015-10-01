module Language.SecreC.TypeChecker.Statement where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base

tcStmt :: Location loc => Type -> Statement loc -> TcM loc (Statement (Typed loc),Type)