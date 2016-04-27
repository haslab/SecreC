{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.Prover.Semantics where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Prover.Base

import Data.Word

evaluateIndexExpr :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> TcM m Word64
evaluateExpr :: (ProverK loc m) => loc -> Expression VarIdentifier (Typed loc) -> TcM m ILit
evaluateIExpr :: (ProverK loc m) => loc -> IExpr -> TcM m ILit