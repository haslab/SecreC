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

tcExpr :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))

tcGuard :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))

tcIndexExpr :: (VarsTcM loc,Location loc) => Expression Identifier loc -> TcM loc (SExpr VarIdentifier (Typed loc),Either SecrecError Word64)

tcExprTy :: (VarsTcM loc,Location loc) => Type -> Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))

tcSizeExpr :: (VarsTcM loc,Location loc) => ComplexType -> Word64 -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc (SExpr VarIdentifier (Typed loc))

tcVarName :: Location loc => VarName Identifier loc -> TcM loc (VarName VarIdentifier (Typed loc))

tcDimExpr :: (VarsTcM loc,Location loc) => Doc -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc (SExpr VarIdentifier (Typed loc))

tcSizes :: (VarsTcM loc,Location loc) => loc -> ComplexType -> Maybe (VarName Identifier loc) -> Maybe Word64 -> Sizes Identifier loc -> TcM loc (Sizes VarIdentifier (Typed loc))