module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Statement

tcGuard :: Location loc => Expression loc -> TcReaderM loc (Expression (Typed loc))
tcGuard e = tcExprTy t e
    where t = CType Public (PrimType $ DatatypeBool ()) 0 Nothing

tcExpr :: Location loc => Expression loc -> TcReaderM loc (Expression (Typed loc),Type)
tcExpr = undefined

-- | evaluates an expression to a literal integer expression
integerLitExpr :: Location loc => Expression loc -> TcReaderM loc (Maybe (Expression loc))
integerLitExpr = undefined

tcExprTy :: Location loc => Type -> Expression loc -> TcReaderM loc (Expression (Typed loc))
tcExprTy ty e = do
    (e',ty') <- tcExpr e
    coerces (loc e) ty' ty
    return e'