module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Statement
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import Language.SecreC.Vars
import Language.SecreC.Utils

import Language.SecreC.Parser.Parsec

import System.IO.Unsafe

import Prelude hiding (mapM)

import Control.Monad hiding (mapAndUnzipM,mapM)

import Data.Monoid
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable

tcGuard :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))
tcGuard e = tcExprTy t e
    where t = CType Public (PrimType $ DatatypeBool ()) (integerExpr 0) []

tcExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))
tcExpr (BinaryAssign l pe op e) = do
    pe' <- tcPostfixExpr pe
    e' <- tcExpr e
    t <- tcReaderM $ tcBinaryAssignOp l op (typed $ loc pe') (typed $ loc e')
    return $ BinaryAssign (Typed l t) pe' op e'
tcExpr (QualifiedAssignExpr l qe) = do
    qe' <- tcReaderM $ tcQualExpr qe
    let t = typed $ loc qe'
    return $ QualifiedAssignExpr (Typed l t) qe'

tcBinaryAssignOp :: loc -> BinaryAssignOp -> Type -> Type -> TcReaderM loc Type
tcBinaryAssignOp l bop t1 t2 = do 
    coerces l t2 t1
    case binAssignOpToOp bop of
        Nothing -> return ()
        Just op -> isSupportedOp op t1
    return t1

tcPostfixExpr :: Location loc => PostfixExpression loc -> TcM loc (PostfixExpression (Typed loc))
tcPostfixExpr (DeclassifyExpr l e) = do
    e' <- tcExpr e
    let et' = typed $ loc e'
    t <- tcReaderM $ declassifyType l et'
    return $ DeclassifyExpr (Typed l t) e'
tcPostfixExpr (SizeExpr l e) = do
    e' <- tcExpr e
    undefined -- TODO
tcPostfixExpr (ShapeExpr l e) = do
    e' <- tcExpr e
    undefined -- TODO
tcPostfixExpr (PostCatExpr l e) = do
    e' <- tcReaderM $ tcCatExpr e
    let t = typed $ loc e'
    return $ PostCatExpr (Typed l t) e'
tcPostfixExpr (DomainIdExpr l s) = do
    s' <- tcReaderM $ tcSecTypeSpec s
    let t = typed $ loc s'
    return $ DomainIdExpr (Typed l t) s'
tcPostfixExpr (ReshapeExpr l es) = undefined -- TODO
tcPostfixExpr (ToStringExpr l e) = undefined -- TODO
tcPostfixExpr (StrlenExpr l e) = undefined -- TODO
tcPostfixExpr (StringFromBytesExpr l e) = undefined -- TODO
tcPostfixExpr (BytesFromStringExpr l e) = undefined -- TODO
tcPostfixExpr call@(ProcCallExpr {}) = do
    b <- insideTemplate
    if b
        then tcProcedureConstraint call
        else tcProcedureResolve call
tcPostfixExpr (PostIndexExpr l e s) = do
    e' <- tcPostfixExpr e
    let t = typed $ loc e'
    (s',t') <- tcSubscript t s
    return $ PostIndexExpr (Typed l t') e' s'
tcPostfixExpr (SelectionExpr l pe a) = do
    pe' <- tcPostfixExpr pe
    let tpe' = typed $ loc pe'
    t <- projectStructField l tpe' a
    return $ SelectionExpr (Typed l t) pe' (fmap notTyped a)
tcPostfixExpr (PostPrimExpr l pe) = do
    pe' <- tcReaderM $ tcPrimExpr pe
    let t = typed $ loc pe'
    return $ PostPrimExpr (Typed l t) pe'

tcProcedureConstraint :: Location loc => PostfixExpression loc -> TcM loc (PostfixExpression (Typed loc))
tcProcedureConstraint (ProcCallExpr l n@(ProcedureName pl pn) es) = undefined
--    es' <- mapM tcExpr es
--    let l' = Typed l t
--    let n' = fmap notTyped n -- we dont't type the procedure name, only the application
--    addTemplateConstraint cstr -- add constraint to the environment 
--    return $ ProcCallExpr l' n' es'

--tcTemplateTypeConstraint (TemplateSpecifier l n@(TypeName tl tn) args) = do
--    args' <- mapM tcTemplateTypeArgument args
--    let t = TApp tn (map (typed . loc) args') mempty
--    let cstr = TCstr (Left tn) (map (typed . loc) args')
--    let l' = Typed l t
--    let n' = fmap notTyped n -- we dont't type the template name, only the application
--    addTemplateConstraint cstr -- add constraint to the environment
--    return $ TemplateSpecifier l' n' args'

tcProcedureResolve :: Location loc => PostfixExpression loc -> TcM loc (PostfixExpression (Typed loc))
tcProcedureResolve (ProcCallExpr l n@(ProcedureName pl pn) es) = do
    es' <- mapM tcExpr es
    let tes = map (typed . loc) es'
    let n' = fmap notTyped n -- we don't type the procedure name, only the application
    (t,pos,_) <- matchTemplateType l pn tes (checkProcedure n) mempty
    let l' = Typed l t
    return $ ProcCallExpr l' n' es'

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: Location loc => Type -> Subscript loc -> TcM loc (Subscript (Typed loc),Type)
tcSubscript t s = do
    (s',rngs) <- mapAndUnzipM tcIndex s
    t' <- projectMatrixType (loc s) t (Foldable.toList rngs)
    return (s',t')

tcIndex :: Location loc => Index loc -> TcM loc (Index (Typed loc),(Maybe Integer,Maybe Integer))
tcIndex (IndexInt l e) = do
    (e',mb) <- integerLitExpr e
    return (IndexInt (notTyped l) e',(mb,mb))
tcIndex (IndexSlice l e1 e2) = do
    let f x = case x of
                Nothing -> (Nothing,Nothing)
                Just (x,mb) -> (Just x,mb)
    (e1',mb1) <- liftM f $ mapM integerLitExpr e1
    (e2',mb2) <- liftM f $ mapM integerLitExpr e2
    return (IndexSlice (notTyped l) e1' e2',(mb1,mb2))

tcCatExpr :: Location loc => CatExpression loc -> TcReaderM loc (CatExpression (Typed loc))
tcCatExpr = undefined -- TODO

tcQualExpr :: Location loc => QualifiedExpression loc -> TcReaderM loc (QualifiedExpression (Typed loc))
tcQualExpr = undefined -- TODO

tcPrimExpr :: Location loc => PrimaryExpression loc -> TcReaderM loc (PrimaryExpression (Typed loc))
tcPrimExpr = undefined -- TODO

-- | returns the operation performed by a binary assignment operation
binAssignOpToOp :: BinaryAssignOp -> Maybe (Op ())
binAssignOpToOp BinaryAssignEqual = Nothing
binAssignOpToOp BinaryAssignMul = Just $ OpMul ()
binAssignOpToOp BinaryAssignDiv = Just $ OpDiv ()
binAssignOpToOp BinaryAssignMod = Just $ OpMod ()
binAssignOpToOp BinaryAssignAdd = Just $ OpAdd ()
binAssignOpToOp BinaryAssignSub = Just $ OpSub ()
binAssignOpToOp BinaryAssignAnd = Just $ OpBand ()
binAssignOpToOp BinaryAssignOr = Just $ OpBor ()
binAssignOpToOp BinaryAssignXor = Just $ OpXor ()

-- | typechecks an expression and tries to evaluate it to a literal integer
integerLitExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc),Maybe Integer)
integerLitExpr = undefined -- TODO

isStaticIntegerExpr :: Location loc => Expression () -> TcM loc (Maybe Integer)
isStaticIntegerExpr e = liftM snd $ integerLitExpr (fmap (const noloc) e)

tcExprTy :: Location loc => Type -> Expression loc -> TcM loc (Expression (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    let ty' = typed $ loc e'
    tcReaderM $ coerces (loc e) ty' ty
    return e'
    
tcDimSizeExpr :: Location loc => Maybe (VarName loc) -> Expression loc -> TcM loc (Expression (Typed loc))
tcDimSizeExpr v sz = do
    (sz',mb) <- integerLitExpr sz
    let ty = typed $ loc sz'
    -- size must be a value of the longest unsigned int
    tcReaderM $ coerces (loc sz) ty largestInt
    -- check if size is static and if so evaluate it
    when (isNothing mb) $ tcWarn (locpos $ loc sz') $ DependentMatrixSize (fmap locpos sz') (fmap (fmap locpos) v)
    return sz'     

-- | constant zero literal
integerExpr :: Integer -> Expression ()
integerExpr i = fmap (const ()) $ unsafePerformIO $ parseSecreCIOWith defaultOptions "" (show i) scExpression