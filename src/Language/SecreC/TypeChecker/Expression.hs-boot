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

tcVariadicArg :: (PP (a VarIdentifier (Typed loc)),VarsIdTcM m,Located (a VarIdentifier (Typed loc)),Location loc,LocOf (a VarIdentifier (Typed loc)) ~ (Typed loc)) => (a Identifier loc -> TcM m (a VarIdentifier (Typed loc))) -> (a Identifier loc,IsVariadic) -> TcM m (a VarIdentifier (Typed loc),IsVariadic)

landExprs :: (ProverK loc m) => loc -> Bool -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)

tcAnnGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcAnnExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

repeatExpr :: ProverK loc m => loc -> Bool -> Expr -> Maybe Expr -> ComplexType -> TcM m Expr

eqExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr

tcExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcPureExpr :: ProverK loc m => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

allExprs :: ProverK loc m => loc -> Bool -> [Expr] -> TcM m Expr

andExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)

andExprsLoc :: Location loc => [Expression iden (Typed loc)] -> Expression iden (Typed loc)

multiplyIndexVariadicExprs :: (ProverK loc m) => loc -> Bool -> [(Expr,IsVariadic)] -> TcM m Expr

classifyExpr :: ProverK loc m => loc -> Bool -> Expr -> ComplexType -> TcM m Expr

reshapeExpr :: ProverK loc m => loc -> Bool -> Expr -> [(Expr,IsVariadic)] -> Type -> TcM m Expr

impliesExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)

tcIndexExpr :: (ProverK loc m) => IsVariadic -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcExprTy :: (ProverK loc m) => Type -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcExprTy' :: (ProverK loc m) => Type -> Expression VarIdentifier (Typed loc) -> TcM m (Expression VarIdentifier (Typed loc))

tcVarName :: (ProverK loc m) => Bool -> VarName Identifier loc -> TcM m (VarName VarIdentifier (Typed loc))

tcSizes :: (ProverK loc m) => loc -> Sizes Identifier loc -> TcM m (Sizes VarIdentifier (Typed loc))

sumIndexExprs :: (ProverK loc m) => loc -> Bool -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)

subtractIndexExprs :: (ProverK loc m) => loc -> Bool -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)

multiplyIndexExprs :: (ProverK loc m) => loc -> Bool -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)

tcIndexCond :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

negBoolExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc)
