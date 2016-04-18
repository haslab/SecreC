{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Statement where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Prover.Base

import Data.Set

tcStmt :: (ProverK loc m) => Type -> Statement Identifier loc -> TcM loc m (Statement VarIdentifier (Typed loc),Type)

