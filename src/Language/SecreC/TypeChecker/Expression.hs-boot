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

landExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)

tcExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcIndexExpr :: (ProverK loc m) => IsVariadic -> Expression Identifier loc -> TcM m (SExpr VarIdentifier (Typed loc))

tcExprTy :: (ProverK loc m) => Type -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))

tcVarName :: (MonadIO m,Location loc) => Bool -> VarName Identifier loc -> TcM m (VarName VarIdentifier (Typed loc))

tcSizes :: (ProverK loc m) => loc -> Type -> Sizes Identifier loc -> TcM m (Sizes VarIdentifier (Typed loc))

sumIndexExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)

subtractIndexExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)

tcIndexCond :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))