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

landExprs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Expression VarIdentifier Type)

tcExpr :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))

tcGuard :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))

tcIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (SExpr VarIdentifier (Typed loc))

tcExprTy :: (VarsIdTcM loc m,Location loc) => Type -> Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))

tcSizeExpr :: (VarsIdTcM loc m,Location loc) => ComplexType -> Word64 -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc m (SExpr VarIdentifier (Typed loc))

tcVarName :: (MonadIO m,Location loc) => Bool -> VarName Identifier loc -> TcM loc m (VarName VarIdentifier (Typed loc))

tcDimExpr :: (VarsIdTcM loc m,Location loc) => Doc -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc m (SExpr VarIdentifier (Typed loc))

tcSizes :: (VarsIdTcM loc m,Location loc) => loc -> ComplexType -> Maybe (VarName Identifier loc) -> Sizes Identifier loc -> TcM loc m (Sizes VarIdentifier (Typed loc))

subtractIndexExprs :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Expression VarIdentifier Type)

tcIndexCond :: (VarsIdTcM loc m,Location loc) => Expression Identifier loc -> TcM loc m (Expression VarIdentifier (Typed loc))