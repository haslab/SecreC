{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Index where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Location
import Language.SecreC.Vars

isIndexType :: Type -> Bool

expr2IExpr :: (Vars (TcM loc) loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc (IExpr VarIdentifier)

expr2ICond :: (Vars (TcM loc) loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc (ICond VarIdentifier)

tryExpr2IExpr :: (Vars (TcM loc) loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc (Either (IExpr VarIdentifier) SecrecError)

tryExpr2ICond :: (Vars (TcM loc) loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc (Either (ICond VarIdentifier) SecrecError)

iExpr2Expr :: (Vars (TcM loc) loc,Location loc) => IExpr VarIdentifier -> TcM loc (Expression VarIdentifier Type)
iCond2Expr :: (Vars (TcM loc) loc,Location loc) => ICond VarIdentifier -> TcM loc (Expression VarIdentifier Type)

(.+.), (.-.), (.*.), (.**.), (./.), (.%.) :: IExpr id -> IExpr id -> IExpr id

(.==.), (./=.), (.<.), (.<=.), (.>.), (.>=.) :: IExpr id -> IExpr id -> ICond id