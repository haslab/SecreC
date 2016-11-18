{-# LANGUAGE ConstraintKinds, FlexibleContexts, RankNTypes #-}

module Language.SecreC.Transformation.Simplify where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Monad
import Language.SecreC.Prover.Base
import Language.SecreC.Position

import Control.Monad.Except
import Control.Monad.Reader as Reader
import Control.Monad.Trans.Control
import Control.Monad.Base

import Data.Typeable

type SimplifyK loc m = ProverK loc m

type SimplifyM m = (TcM m)
type SimplifyCont loc m a = SimplifyK loc m => a -> SimplifyM m ([Statement GIdentifier (Typed loc)],a)
type SimplifyT loc m a = SimplifyCont loc m (a GIdentifier (Typed loc))

type SimplifyG loc m a = SimplifyK loc m => a GIdentifier (Typed loc) -> SimplifyM m (a GIdentifier (Typed loc))

tryRunSimplify :: SimplifyK Position m => (a -> SimplifyM m a) -> (a -> TcM m a)

runSimplify :: SimplifyK Position m => SimplifyM m a -> TcM m a

simplifyExpression :: SimplifyK loc m => Bool -> Expression GIdentifier (Typed loc) -> SimplifyM m ([Statement GIdentifier (Typed loc)],Maybe (Expression GIdentifier (Typed loc)))

simplifyStmts :: SimplifyK loc m => Maybe (VarName GIdentifier (Typed loc)) -> [Statement GIdentifier (Typed loc)] -> SimplifyM m [Statement GIdentifier (Typed loc)]

simplifyInnerDecType :: SimplifyK Position m => InnerDecType -> SimplifyM m InnerDecType

trySimplify :: SimplifyK Position m => (a -> SimplifyM m a) -> (a -> SimplifyM m a)

simplifyNonVoidExpression :: Bool -> SimplifyT loc m Expression

inlineExpr :: SimplifyK loc m => loc -> Expr -> SimplifyM m Expr

tryInlineExpr :: SimplifyK loc m => loc -> Expr -> SimplifyM m (Maybe Expr)

tryInlineLemmaCall :: SimplifyK loc m => loc -> Expression GIdentifier (Typed loc) -> SimplifyM m (Maybe (Maybe DecType,[StatementAnnotation GIdentifier (Typed loc)]))
