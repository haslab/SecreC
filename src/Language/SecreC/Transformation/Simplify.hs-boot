{-# LANGUAGE ConstraintKinds, FlexibleContexts, RankNTypes #-}

module Language.SecreC.Transformation.Simplify where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Monad
import Language.SecreC.Prover.Base

import Control.Monad.Except
import Control.Monad.Reader as Reader
import Control.Monad.Trans.Control
import Control.Monad.Base

import Data.Typeable

type SimplifyK loc m = ProverK loc m

type SimplifyM loc m a = SimplifyK loc m => a -> TcM m ([Statement VarIdentifier (Typed loc)],a)
type SimplifyT loc m a = SimplifyM loc m (a VarIdentifier (Typed loc))

type SimplifyG loc m a = SimplifyK loc m => a VarIdentifier (Typed loc) -> TcM m (a VarIdentifier (Typed loc))

simplifyExpression :: SimplifyK loc m => Expression VarIdentifier (Typed loc) -> TcM m ([Statement VarIdentifier (Typed loc)],Maybe (Expression VarIdentifier (Typed loc)))