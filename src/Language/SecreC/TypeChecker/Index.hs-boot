{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Index where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Location
import Language.SecreC.Vars
import Text.PrettyPrint

isIndexType :: Type -> Bool

expr2IExprAs :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> Type -> TcM loc m (IExpr)

expr2IExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (IExpr)

expr2ICond :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (ICond)

tryExpr2IExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either (IExpr) SecrecError)

tryExpr2ICond :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either (ICond) SecrecError)

(.+.), (.-.), (.*.), (.**.), (./.), (.%.) :: IExpr -> IExpr -> IExpr

(.==.), (./=.), (.<.), (.<=.), (.>.), (.>=.) :: IExpr -> IExpr -> ICond