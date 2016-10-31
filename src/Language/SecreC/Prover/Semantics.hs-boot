{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.Prover.Semantics where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Prover.Base

import Data.Word

fullyEvaluateIndexExpr :: (ProverK loc m) => loc -> Expression GIdentifier Type -> TcM m Word64
fullyEvaluateExpr :: (ProverK loc m) => loc -> Expression GIdentifier (Typed loc) -> TcM m ILit
fullyEvaluateIExpr :: (ProverK loc m) => loc -> IExpr -> TcM m ILit