{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.Prover.Expression where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.Transformation.Simplify

expr2IExpr :: ProverK loc m => Expression GIdentifier (Typed loc) -> TcM m IExpr

expr2SimpleIExpr :: (ProverK loc m) => Expression GIdentifier (Typed loc) -> TcM m IExpr