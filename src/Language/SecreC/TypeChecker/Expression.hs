{-# LANGUAGE TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Statement
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Unification
import Language.SecreC.Vars
import Language.SecreC.Utils

import Prelude hiding (mapM)

import Control.Monad hiding (mapAndUnzipM,mapM)

import Data.Monoid
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import Data.Dynamic

tcGuard :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))
tcGuard e = tcExprTy t e
    where t = PrimType $ DatatypeBool ()

tcExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))
tcExpr (BinaryAssign l pe op e) = do
    pe' <- tcPostfixExpr pe
    e' <- tcExpr e
    t <- tcBinaryAssignOp l op (typed $ loc pe') (typed $ loc e')
    return $ BinaryAssign (Typed l t) pe' op e'
tcExpr (QualExpr l e ts) = error "tcExpr" -- TODO
tcExpr (CondExpr l c e1 e2) = do
    c' <- tcGuard c
    e1' <- tcExpr e1
    let t1 = typed $ loc e1'
    e2' <- tcExpr e2
    let t2 = typed $ loc e2'
    (t,_) <- tcProofM $ coerces2 l t2 t1
    return $ CondExpr (Typed l t) c' e1' e2'
tcExpr (BinaryExpr l e1 op e2) = do
    e1' <- tcExpr e1
    e2' <- tcExpr e2
    (t,_) <- tcProofM $ coerces2 l (typed $ loc e1') (typed $ loc e2')
    tcReaderM $ isSupportedOp (fmap (const ()) op) t
    return $ BinaryExpr (Typed l t) e1' (fmap notTyped op) e2'
tcExpr (PrimCastExpr l t e) = error "tcExpr" -- TODO
tcExpr (VarCastExpr l t e) = error "tcExpr" -- TODO
tcExpr (PrefixInc l e) = error "tcExpr" -- TODO
tcExpr (PrefixDec l e) = error "tcExpr" -- TODO
tcExpr (PostfixInc l e) = error "tcExpr" -- TODO
tcExpr (PostfixDec l e) = error "tcExpr" -- TODO
tcExpr (UminusExpr l e) = error "tcExpr" -- TODO
tcExpr (UnegExpr l e) = error "tcExpr" -- TODO
tcExpr (UinvExpr l e) = error "tcExpr" -- TODO
tcExpr (Upost l pe) = do
    pe' <- tcPostfixExpr pe
    let t = typed $ loc pe'
    return $ Upost (Typed l t) pe'

tcBinaryAssignOp :: Location loc => loc -> BinaryAssignOp -> Type -> Type -> TcM loc Type
tcBinaryAssignOp l bop t1 t2 = do 
    tcProofM $ coerces l t2 t1
    case binAssignOpToOp bop of
        Nothing -> return ()
        Just op -> tcReaderM $ isSupportedOp op t1
    return t1

tcPostfixExpr :: Location loc => PostfixExpression loc -> TcM loc (PostfixExpression (Typed loc))
tcPostfixExpr (DeclassifyExpr l e) = do
    e' <- tcExpr e
    let et' = typed $ loc e'
    t <- tcReaderM $ declassifyType l et'
    return $ DeclassifyExpr (Typed l t) e'
tcPostfixExpr (SizeExpr l e) = do
    e' <- tcExpr e
    error "tcPostfixExpr" -- TODO
tcPostfixExpr (ShapeExpr l e) = do
    e' <- tcExpr e
    error "tcPostfixExpr" -- TODO
tcPostfixExpr (PostCatExpr l e) = do
    e' <- tcReaderM $ tcCatExpr e
    let t = typed $ loc e'
    return $ PostCatExpr (Typed l t) e'
tcPostfixExpr (DomainIdExpr l s) = do
    s' <- tcReaderM $ tcSecTypeSpec s
    let t = typed $ loc s'
    return $ DomainIdExpr (Typed l t) s'
tcPostfixExpr (ReshapeExpr l es) = error "tcPostfixExpr" -- TODO
tcPostfixExpr (ToStringExpr l e) = error "tcPostfixExpr" -- TODO
tcPostfixExpr (StrlenExpr l e) = error "tcPostfixExpr" -- TODO
tcPostfixExpr (StringFromBytesExpr l e) = error "tcPostfixExpr" -- TODO
tcPostfixExpr (BytesFromStringExpr l e) = error "tcPostfixExpr" -- TODO
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
    pe' <- tcPrimExpr pe
    let t = typed $ loc pe'
    return $ PostPrimExpr (Typed l t) pe'

tcProcedureConstraint :: Location loc => PostfixExpression loc -> TcM loc (PostfixExpression (Typed loc))
tcProcedureConstraint (ProcCallExpr l n@(ProcedureName pl pn) es) = do
    es' <- mapM tcExpr es
    let ts = map (typed . loc) es'
    let t = TApp (Right pn) ts mempty
    let cstr = TCstr (Right pn) ts
    let l' = Typed l t
    let n' = fmap notTyped n -- we dont't type the procedure name, only the application
    addTemplateConstraint cstr -- add constraint to the environment 
    return $ ProcCallExpr l' n' es'

tcProcedureResolve :: Location loc => PostfixExpression loc -> TcM loc (PostfixExpression (Typed loc))
tcProcedureResolve (ProcCallExpr l n@(ProcedureName pl pn) es) = do
    es' <- mapM tcExpr es
    let tes = map (typed . loc) es'
    let n' = fmap notTyped n -- we don't type the procedure name, only the application
    (ProcType _ _ ret,pos,_) <- matchTemplateType l (Right pn) tes (checkProcedure n) mempty
    let l' = Typed l ret
    return $ ProcCallExpr l' n' es'

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: Location loc => Type -> Subscript loc -> TcM loc (Subscript (Typed loc),Type)
tcSubscript t s = do
    (s',rngs) <- mapAndUnzipM tcIndex s
    t' <- projectMatrixType (loc s) t (Foldable.toList rngs)
    return (s',t')

tcIndex :: Location loc => Index loc -> TcM loc (Index (Typed loc),(Maybe Integer,Maybe Integer))
tcIndex (IndexInt l e) = do
    (e',mb) <- uintLitExpr e
    return (IndexInt (notTyped l) e',(mb,mb))
tcIndex (IndexSlice l e1 e2) = do
    let f x = case x of
                Nothing -> (Nothing,Nothing)
                Just (x,mb) -> (Just x,mb)
    (e1',mb1) <- liftM f $ mapM uintLitExpr e1
    (e2',mb2) <- liftM f $ mapM uintLitExpr e2
    return (IndexSlice (notTyped l) e1' e2',(mb1,mb2))

tcCatExpr :: Location loc => CatExpression loc -> TcReaderM loc (CatExpression (Typed loc))
tcCatExpr = error "tcCatExpr" -- TODO
    
tcPrimExpr :: Location loc => PrimaryExpression loc -> TcM loc (PrimaryExpression (Typed loc))
tcPrimExpr (PExpr l e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    return (PExpr (Typed l t) e')
tcPrimExpr (ArrayConstructorPExpr l es) = error "tcPrimExpr" -- TODO
tcPrimExpr (RVariablePExpr l v@(VarName vl vn)) = do
    t <- tcReaderM $ checkVariable GlobalScope v
    return $ RVariablePExpr (Typed l t) (VarName (Typed vl t) vn) 
tcPrimExpr (LitPExpr l lit) = do
    lit' <- tcLiteral lit
    let t = typed $ loc lit'
    return $ LitPExpr (Typed l t) lit'

tcLiteral :: Location loc => Literal loc -> TcM loc (Literal (Typed loc))
tcLiteral (IntLit l i) = do
    let t = PrimType $ if i >= 0 then DatatypeUint () else DatatypeInt ()
    return $ IntLit (Typed l t) i
tcLiteral (StringLit l s) = do
    let t = PrimType $ DatatypeString ()
    return $ StringLit (Typed l t) s
tcLiteral (BoolLit l b) = do
    let t = PrimType $ DatatypeBool ()
    return $ BoolLit (Typed l t) b
tcLiteral (FloatLit l f) = do
    let t = PrimType $ DatatypeFloat64 ()
    return $ FloatLit (Typed l t) f

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
uintLitExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc),Maybe Integer)
uintLitExpr e = do
    e' <- tcExprTy largestUint e
    (e'',mb) <- evalUintExpr e' 
    case mb of
        Nothing -> return (e'',Nothing)
        Just i -> return (fmap (const $ Typed noloc largestUint) e'',Just i)

isStaticUintExpr :: Location loc => Expression () -> TcM loc (Maybe Integer)
isStaticUintExpr e = liftM snd $ uintLitExpr (fmap (const noloc) e)

tcExprTy :: Location loc => Type -> Expression loc -> TcM loc (Expression (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    let Typed l ty' = loc e'
    tcProofM $ coerces l ty' ty
    return e'
    
tcDimSizeExpr :: Location loc => Maybe (VarName loc) -> Expression loc -> TcM loc (Expression (Typed loc))
tcDimSizeExpr v sz = do
    (sz',mb) <- uintLitExpr sz
    let ty = typed $ loc sz'
    -- size must be a value of the longest unsigned int
    tcProofM $ coerces (loc sz) ty largestUint
    -- check if size is static and if so evaluate it
    when (isNothing mb) $ tcWarn (locpos $ loc sz') $ DependentMatrixSize (fmap locpos sz') (fmap (fmap locpos) v)
    return sz'     

evalUintExpr :: (Monad m,Location loc) => Expression loc -> m (Expression loc,Maybe Integer)
evalUintExpr e = do
    (e',mb) <- evalExpr e
    return (e',maybe Nothing fromDynamic mb)

evalExpr :: (Monad m,Location loc) => Expression loc -> m (Expression loc,Maybe Dynamic)
evalExpr (BinaryAssign l e1 o e2) = error "evalExpr" -- TODO
evalExpr (QualExpr l e ts) = error "evalExpr" -- TODO
evalExpr (CondExpr l c e1 e2) = error "evalExpr" -- TODO
evalExpr (BinaryExpr l e1 o e2) = error "evalExpr" -- TODO
evalExpr (PrimCastExpr l t e) = error "evalExpr" -- TODO
evalExpr (VarCastExpr l t e) = error "evalExpr" -- TODO
evalExpr (PrefixInc l e) = error "evalExpr" -- TODO
evalExpr (PrefixDec l e) = error "evalExpr" -- TODO
evalExpr (PostfixInc l e) = error "evalExpr" -- TODO
evalExpr (PostfixDec l e) = error "evalExpr" -- TODO
evalExpr (UminusExpr l e) = error "evalExpr" -- TODO
evalExpr (UnegExpr l e) = error "evalExpr" -- TODO
evalExpr (UinvExpr l e) = error "evalExpr" -- TODO
evalExpr (Upost l e) = do
    (e',mb) <- evalPostfixExpr e
    return (Upost l e',mb)

evalPostfixExpr :: (Monad m,Location loc) => PostfixExpression loc -> m (PostfixExpression loc,Maybe Dynamic)
evalPostfixExpr (DeclassifyExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (SizeExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (ShapeExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (PostCatExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (DomainIdExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (ReshapeExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (ToStringExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (StrlenExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (StringFromBytesExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (BytesFromStringExpr l e) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (ProcCallExpr l n es) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (PostIndexExpr l e s) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (SelectionExpr l e a) = error "evalPostfixExpr" -- TODO
evalPostfixExpr (PostPrimExpr l p) = do
    (p',mb) <- evalPrimExpr p
    return (PostPrimExpr l p',mb)

evalPrimExpr :: (Monad m,Location loc) => PrimaryExpression loc -> m (PrimaryExpression loc,Maybe Dynamic)
evalPrimExpr (PExpr l e) = error "evalPrimExpr" -- TODO
evalPrimExpr (ArrayConstructorPExpr l es) = error "evalPrimExpr" -- TODO
evalPrimExpr (RVariablePExpr l v) = error "evalPrimExpr" -- TODO
evalPrimExpr (LitPExpr l lit) = do
    d <- evalLit lit
    return (LitPExpr l lit,Just d)

evalLit :: (Monad m,Location loc) => Literal loc -> m Dynamic
evalLit (IntLit l i) = return $ toDyn i
evalLit (StringLit l s) = return $ toDyn s
evalLit (BoolLit l b) = return $ toDyn b
evalLit (FloatLit l f) = return $ toDyn f

    