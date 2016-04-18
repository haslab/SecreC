{-# LANGUAGE ConstraintKinds, FlexibleContexts, RankNTypes #-}

module Language.SecreC.Transformation.Simplify where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Monad

import Control.Monad.Except
import Control.Monad.Reader as Reader
import Control.Monad.Trans.Control
import Control.Monad.Base

import Data.Typeable

type SimplifyK loc t m = (Monad (t m),Typeable t,MonadTrans t,MonadBaseControl IO m,Typeable m,MonadIO m,Location loc,Vars VarIdentifier (t m) loc,MonadError SecrecError (t m))

type SimplifyM loc t m a = SimplifyK loc t m => a -> t m ([Statement VarIdentifier (Typed loc)],a)
type SimplifyT loc t m a = SimplifyM loc t m (a VarIdentifier (Typed loc))

type SimplifyG loc t m a = SimplifyK loc t m => a VarIdentifier (Typed loc) -> t m (a VarIdentifier (Typed loc))

simplifyExpression :: SimplifyK loc t m => Expression VarIdentifier (Typed loc) -> t m ([Statement VarIdentifier (Typed loc)],Maybe (Expression VarIdentifier (Typed loc)))