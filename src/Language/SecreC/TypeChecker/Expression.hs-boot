{-# LANGUAGE FlexibleContexts, TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.Error

import Data.Int
import Data.Word

tcExpr :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))

tcGuard :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))

tcIndexExpr :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc),Either SecrecError Word64)

tcExprTy :: (VarsTcM loc,Location loc) => Type -> Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))

tcSizeExpr :: (VarsTcM loc,Location loc) => ComplexType -> Word64 -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))

tcVarName :: Location loc => VarName Identifier loc -> TcM loc (VarName VarIdentifier (Typed loc))