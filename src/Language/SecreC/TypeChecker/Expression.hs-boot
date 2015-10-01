module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base

tcExpr :: Location loc => Expression loc -> TcReaderM loc (Expression (Typed loc),Type)

tcGuard :: Location loc => Expression loc -> TcReaderM loc (Expression (Typed loc))

integerLitExpr :: Location loc => Expression loc -> TcReaderM loc (Maybe (Expression loc))

tcExprTy :: Location loc => Type -> Expression loc -> TcReaderM loc (Expression (Typed loc))