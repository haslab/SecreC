{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.Prover.Semantics where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Prover.Base

import Data.Word

evaluateIndexExpr :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> TcM loc m Word64