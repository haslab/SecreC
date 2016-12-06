{-# LANGUAGE FlexibleContexts, TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Prover.Base

import Text.PrettyPrint

import Data.Int
import Data.Word

import Control.Monad.IO.Class

tcVariadicArg :: (PP (TcM m) (a GIdentifier (Typed loc)),VarsGTcM m,Located (a GIdentifier (Typed loc)),Location loc,LocOf (a GIdentifier (Typed loc)) ~ (Typed loc)) => (a Identifier loc -> TcM m (a GIdentifier (Typed loc))) -> (a Identifier loc,IsVariadic) -> TcM m (a GIdentifier (Typed loc),IsVariadic)

landExprs :: (ProverK loc m) => loc -> Bool -> Expression GIdentifier Type -> Expression GIdentifier Type -> TcM m (Expression GIdentifier Type)

tcAnnGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

tcAnnExpr :: (ProverK loc m) => Maybe Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

repeatExpr :: ProverK loc m => loc -> Bool -> Expr -> Maybe Expr -> ComplexType -> TcM m Expr

eqExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr

tcExpr :: (ProverK loc m) => Maybe Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

tcPureExpr :: ProverK loc m => Maybe Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

tcGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

allExprs :: ProverK loc m => loc -> Bool -> [Expr] -> TcM m Expr

andExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)

andExprsLoc :: Location loc => [Expression iden (Typed loc)] -> Expression iden (Typed loc)

multiplyIndexVariadicExprs :: (ProverK loc m) => loc -> Bool -> [(Expr,IsVariadic)] -> TcM m Expr

classifyExpr :: ProverK loc m => loc -> Bool -> Expr -> ComplexType -> TcM m Expr

reshapeExpr :: ProverK loc m => loc -> Bool -> Expr -> [(Expr,IsVariadic)] -> Type -> TcM m Expr

impliesExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)

tcIndexExpr :: (ProverK loc m) => IsVariadic -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

tcExprTy :: (ProverK loc m) => Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

tcExprTy' :: (ProverK loc m) => Type -> Expression GIdentifier (Typed loc) -> TcM m (Expression GIdentifier (Typed loc))

tcVarName :: (ProverK loc m) => Bool -> VarName Identifier loc -> TcM m (VarName GIdentifier (Typed loc))

tcSizes :: (ProverK loc m) => loc -> Sizes Identifier loc -> TcM m (Sizes GIdentifier (Typed loc))

sumIndexExprs :: (ProverK loc m) => loc -> Bool -> Expression GIdentifier Type -> Expression GIdentifier Type -> TcM m (Expression GIdentifier Type)

subtractIndexExprs :: (ProverK loc m) => loc -> Bool -> Expression GIdentifier Type -> Expression GIdentifier Type -> TcM m (Expression GIdentifier Type)

multiplyIndexExprs :: (ProverK loc m) => loc -> Bool -> Expression GIdentifier Type -> Expression GIdentifier Type -> TcM m (Expression GIdentifier Type)

tcIndexCond :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))

negBoolExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc)
