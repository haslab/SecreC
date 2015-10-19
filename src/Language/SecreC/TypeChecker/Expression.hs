module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Statement

import Language.SecreC.Parser.Parsec

import System.IO.Unsafe

tcGuard :: Location loc => Expression loc -> TcReaderM loc (Expression (Typed loc))
tcGuard e = tcExprTy t e
    where t = CType Public (PrimType $ DatatypeBool ()) zeroExpr Nothing

tcExpr :: Location loc => Expression loc -> TcReaderM loc (Expression (Typed loc),Type)
tcExpr = undefined

-- | evaluates an expression to a literal integer expression
integerLitExpr :: Location loc => Expression loc -> TcReaderM loc (Maybe (Expression loc,Int))
integerLitExpr = undefined

tcExprTy :: Location loc => Type -> Expression loc -> TcReaderM loc (Expression (Typed loc))
tcExprTy ty e = do
    (e',ty') <- tcExpr e
    coerces (loc e) ty' ty
    return e'
    
tcDimSizeExpr :: Location loc => Maybe (VarName loc) -> Expression loc -> TcM loc (Expression (Typed loc))
tcDimSizeExpr v sz = do
    (sz',ty) <- tcReaderM $ tcExpr sz
    -- size must be a value of the longest unsigned int
    tcReaderM $ coerces (loc sz) ty largestInt
    -- check if size is static and if so evaluate it
    mb <- tcLocM notTyped unTyped $ tcReaderM $ integerLitExpr sz'
    case mb of
        Nothing -> do
            tcWarn (locpos $ loc sz') $ DependentDimensionSize (fmap locpos sz') (fmap (fmap locpos) v)
            return sz'
        Just (isz',_) -> return isz'     

-- | constant zero literal
zeroExpr :: Expression ()
zeroExpr = fmap (const ()) $ unsafePerformIO $ parseSecreCIOWith defaultOptions "" "0" scExpression