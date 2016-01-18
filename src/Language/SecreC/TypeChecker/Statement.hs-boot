{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Statement where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.TypeChecker.Base

tcStmt :: (VarsIdTcM loc m,Location loc) => Type -> Statement Identifier loc -> TcM loc m (Statement VarIdentifier (Typed loc),Type)

