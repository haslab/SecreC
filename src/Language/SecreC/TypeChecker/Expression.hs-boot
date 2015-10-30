{-# LANGUAGE TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base

tcExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))

tcGuard :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))

uintLitExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc),Maybe Integer)

tcExprTy :: Location loc => Type -> Expression loc -> TcM loc (Expression (Typed loc))

tcDimSizeExpr :: Location loc => Maybe (VarName loc) -> Expression loc -> TcM loc (Expression (Typed loc))

isStaticUintExpr :: Location loc => Expression () -> TcM loc (Maybe Integer)