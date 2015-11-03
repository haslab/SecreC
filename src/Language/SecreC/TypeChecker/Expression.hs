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
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.Vars
import Language.SecreC.Utils

import Prelude hiding (mapM)

import Control.Monad hiding (mapAndUnzipM,mapM)
import Control.Monad.IO.Class

import Data.Monoid
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map

tcGuard :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))
tcGuard e = tcExprTy boolType e

tcExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc))
tcExpr (BinaryAssign l pe op e) = do
    pe' <- tcPostfixExpr pe
    e' <- tcExpr e
    t <- tcBinaryAssignOp l op (typed $ loc pe') (typed $ loc e')
    return $ BinaryAssign (Typed l t) pe' op e'
tcExpr (QualExpr l e ts) = genericError (locpos l) "tcExprQual"-- TODO
tcExpr (CondExpr l c e1 e2) = do
    c' <- tcGuard c
    e1' <- tcExpr e1
    let t1 = typed $ loc e1'
    e2' <- tcExpr e2
    let t2 = typed $ loc e2'
    t <- tcCstrM l $ Coerces2 t2 t1
    return $ CondExpr (Typed l t) c' e1' e2'
tcExpr (BinaryExpr l e1 op e2) = do
    e1' <- tcExpr e1
    e2' <- tcExpr e2
    t <- tcCstrM l $ Coerces2 (typed $ loc e1') (typed $ loc e2')
    ret <- tcCstrM l $ SupportedOp (fmap (const ()) op) t
    return $ BinaryExpr (Typed l ret) e1' (fmap notTyped op) e2'
tcExpr (PrimCastExpr l p e) = do
    e' <- tcExpr e
    let te = typed $ loc e'
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    ret <- tcCstrM l $ Cast te t
    return $ PrimCastExpr (Typed l t) p' e'
tcExpr (VarCastExpr l v e) = do
    e' <- tcExpr e
    let te = typed $ loc e'
    v' <- tcTypeName v
    let t = typed $ loc v'
    ret <- tcCstrM l $ Cast te t
    return $ VarCastExpr (Typed l t) v' e'
tcExpr (PrefixInc l e) = genericError (locpos l) "tcExprPredInc" -- TODO
tcExpr (PrefixDec l e) = genericError (locpos l) "tcExprPreDec" -- TODO
tcExpr (PostfixInc l e) = genericError (locpos l) "tcExprPostInc" -- TODO
tcExpr (PostfixDec l e) = genericError (locpos l) "tcExprPostDec" -- TODO
tcExpr (UminusExpr l e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    ret <- tcCstrM l $ SupportedOp (OpSub ()) t
    return $ UminusExpr (Typed l ret) e'
tcExpr (UnegExpr l e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    ret <- tcCstrM l $ SupportedOp (OpNot ()) t
    tcReaderM $ return $ UnegExpr (Typed l ret) e'
tcExpr (UinvExpr l e) = genericError (locpos l) "tcExprUinv" -- TODO
tcExpr (Upost l pe) = do
    pe' <- tcPostfixExpr pe
    let t = typed $ loc pe'
    return $ Upost (Typed l t) pe'

tcBinaryAssignOp :: Location loc => loc -> BinaryAssignOp -> Type -> Type -> TcM loc Type
tcBinaryAssignOp l bop t1 t2 = do 
    tcCstrM l $ Coerces t2 t1
    tcCstrM l $ SupportedOp (binAssignOpToOp bop) t1

tcPostfixExpr :: Location loc => PostfixExpression loc -> TcM loc (PostfixExpression (Typed loc))
tcPostfixExpr (DeclassifyExpr l e) = do
    e' <- tcExpr e
    let et' = typed $ loc e'
    t <- tcCstrM l $ Declassify et'
    return $ DeclassifyExpr (Typed l t) e'
tcPostfixExpr (SizeExpr l e) = do
    e' <- tcExpr e
    tcCstrM l $ SupportedSize (typed $ loc e')
    return $ SizeExpr (Typed l indexType) e'
tcPostfixExpr (ShapeExpr l e) = do
    e' <- tcExpr e
    genericError (locpos l) $ "tcPostfixExprShape" -- TODO
tcPostfixExpr (PostCatExpr l e) = do
    e' <- tcReaderM $ tcCatExpr e
    let t = typed $ loc e'
    return $ PostCatExpr (Typed l t) e'
tcPostfixExpr (DomainIdExpr l s) = do
    s' <- tcReaderM $ tcSecTypeSpec s
    let t = typed $ loc s'
    return $ DomainIdExpr (Typed l t) s'
tcPostfixExpr (ReshapeExpr l es) = genericError (locpos l) $ "tcPostfixExprReshape" -- TODO
tcPostfixExpr (ToStringExpr l e) = do
    e' <- tcExpr e
    tcCstrM l $ SupportedToString (typed $ loc e')
    return $ ToStringExpr (Typed l stringType) e'
tcPostfixExpr (StrlenExpr l e) = do
    e' <- tcExprTy stringType e
    return $ StrlenExpr (Typed l indexType) e'
tcPostfixExpr (StringFromBytesExpr l e) = do
    e' <- tcExprTy bytesType e
    return $ StringFromBytesExpr (Typed l stringType) e'
tcPostfixExpr (BytesFromStringExpr l e) = do
    e' <- tcExprTy stringType e
    return $ BytesFromStringExpr (Typed l bytesType) e'
tcPostfixExpr call@(ProcCallExpr l n@(ProcedureName pl pn) es) = do
    es' <- mapM tcExpr es
    let ts = map (typed . loc) es'
    ret <- tcCstrM l $ PApp pn ts Nothing -- we don't know the return type on application
    dec <- tcCstrM l $ PDec pn ts Nothing -- we don't know the return type on application
    return $ ProcCallExpr (Typed l ret) (fmap (flip Typed dec) n) es'
tcPostfixExpr (PostIndexExpr l e s) = do
    e' <- tcPostfixExpr e
    let t = typed $ loc e'
    (s',t') <- tcSubscript t s
    return $ PostIndexExpr (Typed l t') e' s'
tcPostfixExpr (SelectionExpr l pe a) = do
    pe' <- tcPostfixExpr pe
    let tpe' = typed $ loc pe'
    t <- tcCstrM l $ ProjectStruct tpe' (fmap (const ()) a)
    return $ SelectionExpr (Typed l t) pe' (fmap notTyped a)
tcPostfixExpr (PostPrimExpr l pe) = do
    pe' <- tcPrimExpr pe
    let t = typed $ loc pe'
    return $ PostPrimExpr (Typed l t) pe'

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: Location loc => Type -> Subscript loc -> TcM loc (Subscript (Typed loc),Type)
tcSubscript t s = do
    (s',rngs) <- mapAndUnzipM tcIndex s
    t' <- tcCstrM (loc s) $ ProjectMatrix t (Foldable.toList rngs)
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
tcPrimExpr (RVariablePExpr l v) = do
    v' <- tcVarName v
    let t = typed $ loc v'
    return $ RVariablePExpr (Typed l t) v'
tcPrimExpr (LitPExpr l lit) = do
    lit' <- tcLiteral lit
    let t = typed $ loc lit'
    return $ LitPExpr (Typed l t) lit'

tcLiteral :: Location loc => Literal loc -> TcM loc (Literal (Typed loc))
tcLiteral (IntLit l i) = do
    let t = TyLit (IntLit () i)
    return $ IntLit (Typed l t) i
tcLiteral (StringLit l s) = do
    let t = PrimType $ DatatypeString ()
    return $ StringLit (Typed l t) s
tcLiteral (BoolLit l b) = do
    let t = PrimType $ DatatypeBool ()
    return $ BoolLit (Typed l t) b
tcLiteral (FloatLit l f) = do
    let t = TyLit (FloatLit () f)
    return $ FloatLit (Typed l t) f

tcVarName :: Location loc => VarName loc -> TcM loc (VarName (Typed loc))
tcVarName v@(VarName l n) = do
    t <- tcReaderM $ checkVariable LocalScope v
    return $ VarName (Typed l t) n

tcTypeName :: Location loc => TypeName loc -> TcM loc (TypeName (Typed loc))
tcTypeName v@(TypeName l n) = do
    t <- tcReaderM $ checkNonTemplateType v
    return $ TypeName (Typed l t) n

-- | returns the operation performed by a binary assignment operation
binAssignOpToOp :: BinaryAssignOp -> Op ()
binAssignOpToOp BinaryAssignEqual = OpEq ()
binAssignOpToOp BinaryAssignMul = OpMul ()
binAssignOpToOp BinaryAssignDiv = OpDiv ()
binAssignOpToOp BinaryAssignMod = OpMod ()
binAssignOpToOp BinaryAssignAdd = OpAdd ()
binAssignOpToOp BinaryAssignSub = OpSub ()
binAssignOpToOp BinaryAssignAnd = OpBand ()
binAssignOpToOp BinaryAssignOr = OpBor ()
binAssignOpToOp BinaryAssignXor = OpXor ()

-- | typechecks an expression and tries to evaluate it to a literal integer
uintLitExpr :: Location loc => Expression loc -> TcM loc (Expression (Typed loc),Maybe Integer)
uintLitExpr e = do
    e' <- tcExprTy indexType e
    (e'',mb) <- evalUintExpr e' 
    case mb of
        Nothing -> return (e'',Nothing)
        Just i -> return (fmap (const $ Typed noloc indexType) e'',Just i)

isStaticUintExpr :: Location loc => Expression () -> TcM loc (Maybe Integer)
isStaticUintExpr e = liftM snd $ uintLitExpr (fmap (const noloc) e)

tcExprTy :: Location loc => Type -> Expression loc -> TcM loc (Expression (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    let Typed l ty' = loc e'
    tcCstrM l $ Coerces ty' ty
    return e'
    
tcDimSizeExpr :: Location loc => Maybe (VarName loc) -> Expression loc -> TcM loc (Expression (Typed loc))
tcDimSizeExpr v sz = do
    (sz',mb) <- uintLitExpr sz
    let ty = typed $ loc sz'
    -- size must be a value of the longest unsigned int
    tcCstrM (loc sz) $ Coerces ty indexType
    -- check if size is static and if so evaluate it
    when (isNothing mb) $ tcWarn (locpos $ loc sz') $ DependentMatrixSize (fmap locpos sz') (fmap (fmap locpos) v)
    return sz'     

evalUintExpr :: (Monad m,Location loc) => Expression loc -> m (Expression loc,Maybe Integer)
evalUintExpr e = do
    (e',mb) <- evalExpr e
    return (e',maybe Nothing fromEqDyn mb)

evalExpr :: (Monad m,Location loc) => Expression loc -> m (Expression loc,Maybe EqDyn)
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

evalPostfixExpr :: (Monad m,Location loc) => PostfixExpression loc -> m (PostfixExpression loc,Maybe EqDyn)
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

evalPrimExpr :: (Monad m,Location loc) => PrimaryExpression loc -> m (PrimaryExpression loc,Maybe EqDyn)
evalPrimExpr (PExpr l e) = error "evalPrimExpr" -- TODO
evalPrimExpr (ArrayConstructorPExpr l es) = error "evalPrimExpr" -- TODO
evalPrimExpr e@(RVariablePExpr l v) = return (e,Nothing)
evalPrimExpr (LitPExpr l lit) = do
    d <- evalLit lit
    return (LitPExpr l lit,Just d)

evalLit :: (Monad m,Location loc) => Literal loc -> m EqDyn
evalLit (IntLit l i) = return $ toEqDyn i
evalLit (StringLit l s) = return $ toEqDyn s
evalLit (BoolLit l b) = return $ toEqDyn b
evalLit (FloatLit l f) = return $ toEqDyn f

