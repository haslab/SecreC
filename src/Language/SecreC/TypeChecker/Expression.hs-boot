{-# LANGUAGE FlexibleContexts, TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Pretty

import Text.PrettyPrint

import Data.Int
import Data.Word

import Control.Monad.IO.Class

tcVariadicArg :: (PP (a VarIdentifier (Typed loc)),VarsIdTcM loc m,Located (a VarIdentifier (Typed loc)),Location loc,LocOf (a VarIdentifier (Typed loc)) ~ (Typed loc)) => (a Identifier loc -> TcM loc m (a VarIdentifier (Typed loc))) -> (a Identifier loc,IsVariadic) -> TcM loc m (a VarIdentifier (Typed loc),IsVariadic)

landExprs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Expression VarIdentifier Type)

tcExpr :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))

tcGuard :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))

tcIndexExpr :: (VarsIdTcM loc m,Location loc) => IsVariadic -> Expression Identifier loc -> TcM loc m (SExpr VarIdentifier (Typed loc))

tcExprTy :: (VarsIdTcM loc m,Location loc) => Type -> Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))

tcVarName :: (MonadIO m,Location loc) => Bool -> VarName Identifier loc -> TcM loc m (VarName VarIdentifier (Typed loc))

tcSizes :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Sizes Identifier loc -> TcM loc m (Sizes VarIdentifier (Typed loc))

subtractIndexExprs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Expression VarIdentifier Type)

tcIndexCond :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))