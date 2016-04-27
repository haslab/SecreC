{-# LANGUAGE ViewPatterns, FlexibleContexts, DataKinds, TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Statement
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.Vars
import Language.SecreC.Utils

import Prelude hiding (mapM)

import Control.Monad hiding (mapAndUnzipM,mapM)
import Control.Monad.IO.Class

import Data.Bifunctor
import Data.Monoid hiding ((<>))
import Data.Either
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Int
import Data.Word

import Text.PrettyPrint as PP

tcGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcGuard e = tcExprTy (BaseT bool) e

tcLValue :: (ProverK loc m) => Bool -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcLValue isConst (PostIndexExpr l e s) = tcNoDeps $ do
    e' <- tcAddDeps l "lvalue" $ tcLValue False e
    let t = typed $ loc e'
    (s',t') <- tcSubscript e' s
    return $ PostIndexExpr (Typed l t') e' s'
tcLValue isConst (SelectionExpr l pe a) = do
    let va = bimap mkVarId id a
    pe' <- tcLValue False pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    res <- newTyVar Nothing
    tcTopCstrM l $ ProjectStruct ctpe' (funit va) res
    return $ SelectionExpr (Typed l res) pe' (fmap (notTyped "tcLValue") va)
tcLValue isConst (RVariablePExpr l v) = do
    v' <- tcVarName isConst v
    let t = typed $ loc v'
    return $ RVariablePExpr (Typed l t) v'
tcLValue isConst e = genTcError (locpos $ loc e) $ text "Not a l-value expression: " <+> quotes (pp e)

tcVariadicArg :: (PP (a VarIdentifier (Typed loc)),VarsIdTcM m,Located (a VarIdentifier (Typed loc)),Location loc,LocOf (a VarIdentifier (Typed loc)) ~ (Typed loc)) => (a Identifier loc -> TcM m (a VarIdentifier (Typed loc))) -> (a Identifier loc,IsVariadic) -> TcM m (a VarIdentifier (Typed loc),IsVariadic)
tcVariadicArg tcA (e,isVariadic) = do
    e' <- tcA e
    let (Typed l t) = loc e'
    if isVariadic
        then unless (isVATy t) $ genTcError (locpos l) $ text "Expression" <+> quotes (pp e' `ppOf` pp t) <+> text "should be variadic"
        else when (isVATy t) $ genTcError (locpos l) $ text "Expression" <+> quotes (pp e' `ppOf` pp t) <+> text "should not be variadic" 
    return (e',isVariadic)

tcExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcExpr (BinaryAssign l pe op e) = do
    pe' <- tcLValue True pe
    let tpe' = typed $ loc pe'
    e' <- tcExpr e
    (eres,op') <- tcBinaryAssignOp l op pe' e'
    return $ BinaryAssign (Typed l tpe') pe' op' eres
tcExpr (QualExpr l e t) = do
    e' <- tcExpr e
    t' <- tcTypeSpec t False
    let ty = typed $ loc t'
    x <- newTypedVar "qex" ty $ Just $ pp e'
    tcTopCstrM l $ Coerces (fmap typed e') x
    return $ QualExpr (Typed l ty) (fmap (Typed l) $ varExpr x) t'
tcExpr (CondExpr l c e1 e2) = do
    (c',cstrsc) <- tcWithCstrs l "condexpr" $ tcGuard c
    e1' <- withDeps LocalScope $ do
        tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed c'
        tcExpr e1
    let t1 = typed $ loc e1'
    e2' <- withDeps LocalScope $ do
        tryAddHypothesis l LocalScope cstrsc $ HypNotCondition $ fmap typed c'
        tcExpr e2
    let t2 = typed $ loc e2'
    t3 <- newTyVar Nothing
    x1 <- newTypedVar "then" t3 $ Just $ pp e1'
    x2 <- newTypedVar "else" t3 $ Just $ pp e2'
    tcTopCstrM l $ Coerces2 (fmap typed e1') (fmap typed e2') x1 x2
    let ex1 = fmap (Typed l) $ varExpr x1
    let ex2 = fmap (Typed l) $ varExpr x2
    return $ CondExpr (Typed l t3) c' ex1 ex2
tcExpr (BinaryExpr l e1 op e2) = do
    e1' <- tcExpr e1
    e2' <- tcExpr e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    top <- tcOp op
    v <- newTyVar Nothing
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [(fmap typed e1',False),(fmap typed e2',False)] v
    return $ BinaryExpr (Typed l v) (fmap (Typed l) x1) (updLoc top (Typed l $ DecT dec)) (fmap (Typed l) x2)
tcExpr (PreOp l op e) = do
    e' <- tcLValue False e
    let t = typed $ loc e'
    (e'',op') <- tcBinaryOp l op e'
    let t' = typed $ loc e''
    return $ PreOp (Typed l t) op' e''
tcExpr (PostOp l op e) = do
    e' <- tcLValue False e
    let t = typed $ loc e'
    (e'',op') <- tcBinaryOp l op e'
    let t' = typed $ loc e''
    return $ PostOp (Typed l t) op' e''
tcExpr (UnaryExpr l op e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    top <- tcOp op
    case (top,t) of
--        (OpCast lcast cast,isLitType -> True) -> do
--            b <- typeToBaseType (unTyped lcast) $ typed $ loc cast
--            s <- newDomainTyVar AnyKind Nothing
--            dim <- newDimVar Nothing
--            let ct = ComplexT $ CType s b dim
--            x <- newTypedVar "cast" ct $ Just $ pp e'
--            tcTopCstrM l $ Coerces (fmap typed e') x
--            let ex = fmap (Typed l) $ RVariablePExpr ct x
--            return $ UnaryExpr (Typed l ct) top ex
        otherwise -> do
            v <- newTyVar Nothing
            (dec,[(x,_)]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [(fmap typed e',False)] v
            let ex = fmap (Typed l) x
            return $ UnaryExpr (Typed l v) (updLoc top (Typed l $ DecT dec)) ex
tcExpr (DomainIdExpr l s) = do
    s' <- tcSecType s
    let t = BaseT index
    return $ DomainIdExpr (Typed l t) s'
tcExpr (StringFromBytesExpr l e) = do
    e' <- tcExprTy (ComplexT bytes) e
    return $ StringFromBytesExpr (Typed l $ BaseT string) e'
tcExpr (BytesFromStringExpr l e) = do
    e' <- tcExprTy (BaseT string) e
    return $ BytesFromStringExpr (Typed l $ ComplexT bytes) e'
tcExpr (VArraySizeExpr l e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    unless (isVATy t) $ genTcError (locpos l) $ text "size... expects a variadic array but got" <+> quotes (pp e)
    sz <- typeSize l t
    return $ fmap (Typed l) sz
tcExpr (QuantifiedExpr l q vs e) = tcLocal $ do
    q' <- tcQuantifier q
    vs' <- mapM tcQVar vs
    e' <- tcGuard e
    return $ QuantifiedExpr (Typed l $ BaseT bool) q' vs' e'
  where
    tcQVar (t,v) = do
        t' <- tcTypeSpec t False
        let ty = typed $ loc t'
        let v' = bimap mkVarId (flip Typed ty) v
        tcTopCstrM l $ IsPublic (fmap typed $ varExpr v') 
        newVariable LocalScope v' Nothing True -- don't add values to the environment
        return (t',v')
tcExpr (LeakExpr l e) = do
    e' <- tcExpr e
    return $ LeakExpr (Typed l $ BaseT bool) e'
tcExpr (VArrayExpr l e sz) = do
    e' <- tcExpr e
    sz' <- tcIndexExpr False sz
    let t = typed $ loc e'
    b <- newBaseTyVar Nothing
    tcTopCstrM l $ TypeBase t b
    let vt = VAType (BaseT b) (fmap typed sz')
    return $ VArrayExpr (Typed l vt) e' sz'
tcExpr call@(ProcCallExpr l n@(ProcedureName pl pn) specs es) = do
    let vn = bimap mkVarId id n
    specs' <- mapM (mapM (tcVariadicArg tcTemplateTypeArgument)) specs
    es' <- mapM (tcVariadicArg tcExpr) es
    let tspecs = fmap (map (mapFst (typed . loc))) specs'
    v <- newTyVar Nothing
    (dec,xs) <- tcTopPDecCstrM l True (Left $ procedureNameId vn) tspecs (map (mapFst (fmap typed)) es') v
    let exs = map (mapFst (fmap (Typed l))) xs
    return $ ProcCallExpr (Typed l v) (fmap (flip Typed (DecT dec)) vn) specs' exs
tcExpr (PostIndexExpr l e s) = tcNoDeps $ do
    e' <- tcAddDeps l "postindex" $ tcExpr e
    let t = typed $ loc e'
    (s',t') <- tcSubscript e' s
    return $ PostIndexExpr (Typed l t') e' s'
tcExpr (SelectionExpr l pe a) = do
    let va = bimap mkVarId id a
    pe' <- tcExpr pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    res <- newTyVar Nothing
    tcTopCstrM l $ ProjectStruct ctpe' (funit va) res
    return $ SelectionExpr (Typed l res) pe' (fmap (notTyped "tcExpr") va)
tcExpr (ArrayConstructorPExpr l es) = do
    lit' <- tcArrayLiteral l es
    return lit'
tcExpr (LitPExpr l lit) = do
    lit' <- tcLiteral lit
    return lit'
tcExpr e = tcLValue False e

tcQuantifier :: ProverK loc m => Quantifier loc -> TcM m (Quantifier (Typed loc))
tcQuantifier (ForallQ l) = return $ ForallQ (notTyped "quantifier" l)
tcQuantifier (ExistsQ l) = return $ ExistsQ (notTyped "quantifier" l)

tcBinaryAssignOp :: (ProverK loc m) => loc -> BinaryAssignOp loc -> Expression VarIdentifier (Typed loc) -> (Expression VarIdentifier (Typed loc)) -> TcM m (Expression VarIdentifier (Typed loc),BinaryAssignOp (Typed loc))
tcBinaryAssignOp l bop lv1 e2 = do 
    let t1 = typed $ loc lv1
    let t2 = typed $ loc e2
    let mb_op = binAssignOpToOp bop
    (eres,dec) <- case mb_op of
        Just op -> do
            top <- tcOp $ fmap (const l) op
            (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [(fmap typed lv1,False),(fmap typed e2,False)] t1
            let ex2 = fmap (Typed l) x2
            return (ex2,DecT dec)
        Nothing -> do
            x1 <- newTypedVar "assign" t1 $ Just $ pp e2
            tcTopCstrM l $ Coerces (fmap typed e2) x1
            let ex1 = fmap (Typed l) $ RVariablePExpr t1 x1
            return (ex1,NoType "bequal")
    return (eres,fmap (flip Typed dec) bop)
    
tcBinaryOp :: (ProverK loc m) => loc -> Op Identifier loc -> Expression VarIdentifier (Typed loc) -> TcM m (Expression VarIdentifier (Typed loc),Op VarIdentifier (Typed loc))
tcBinaryOp l op e1 = do 
    let t1 = typed $ loc e1
    top <- tcOp op
    let elit1 = LitPExpr t1 $ IntLit t1 1
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ fmap typed top) Nothing [(fmap typed e1,False),(elit1,False)] t1
    let ex1 = fmap (Typed l) x1
    return (ex1,updLoc top (Typed l $ DecT dec))

tcOp :: (ProverK loc m) => Op Identifier loc -> TcM m (Op VarIdentifier (Typed loc))
tcOp (OpCast l t) = do
    t' <- tcCastType t
    return $ OpCast (notTyped "tcOp" l) t'
tcOp op = return $ bimap (mkVarId) (notTyped "tcOp") op

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: (ProverK loc m) => Expression VarIdentifier (Typed loc) -> Subscript Identifier loc -> TcM m (Subscript VarIdentifier (Typed loc),Type)
tcSubscript e s = do
    let t = typed $ loc e
    let l = loc s
    ((s',rngs),ks) <- tcWithCstrs l "subscript" $ mapAndUnzipM tcIndex s
    ret <- newTyVar Nothing
    withDependencies ks $ tcTopCstrM l $ ProjectMatrix t (Foldable.toList rngs) ret
    return (s',ret)

tcIndex :: (ProverK loc m) => Index Identifier loc -> TcM m (Index VarIdentifier (Typed loc),ArrayProj)
tcIndex (IndexInt l e) = do
    e' <- tcIndexExpr False e
    let ei = DynArrayIndex (fmap typed e')
    return (IndexInt (notTyped "tcIndex" l) e',ArrayIdx ei)
tcIndex (IndexSlice l e1 e2) = do
    let f x = case x of
                Nothing -> return (Nothing,NoArrayIndex)
                Just y -> do
                    return (Just y,DynArrayIndex (fmap typed y))
    (e1',mb1) <- f =<< mapM (tcIndexExpr False) e1
    (e2',mb2) <- f =<< mapM (tcIndexExpr False) e2
    return (IndexSlice (notTyped "tcIndex" l) e1' e2',ArraySlice mb1 mb2)

tcLiteral :: (ProverK loc m) => Literal loc -> TcM m (Expression VarIdentifier (Typed loc))
tcLiteral li = do
    let l = loc li
    x <- newBaseTyVar Nothing
    sz <- newSizeVar Nothing
    let t = ComplexT $ CType Public x sz
    let elit = LitPExpr t $ fmap (const t) li
    tcTopCstrM l $ CoercesLit elit
    return $ LitPExpr (Typed l t) $ fmap (const (Typed l t)) li

tcArrayLiteral :: (ProverK loc m) => loc -> [Expression Identifier loc] -> TcM m (Expression VarIdentifier (Typed loc))
tcArrayLiteral l es = do
    es' <- mapM tcExpr es
    let es'' = fmap (fmap typed) es'
    x <- newBaseTyVar Nothing
    let t = ComplexT $ CType Public x (indexSExpr 1)
    let elit = ArrayConstructorPExpr t es''
    tcTopCstrM l $ CoercesLit elit
    return $ ArrayConstructorPExpr (Typed l t) es'

tcVarName :: (MonadIO m,Location loc) => Bool -> VarName Identifier loc -> TcM m (VarName VarIdentifier (Typed loc))
tcVarName isConst v@(VarName l n) = checkVariable isConst LocalScope (bimap mkVarId id v)

-- | returns the operation performed by a binary assignment operation
binAssignOpToOp :: BinaryAssignOp loc -> Maybe (Op iden loc)
binAssignOpToOp (BinaryAssignEqual l) = Nothing
binAssignOpToOp (BinaryAssignMul l) = Just $ OpMul l
binAssignOpToOp (BinaryAssignDiv l) = Just $ OpDiv l
binAssignOpToOp (BinaryAssignMod l) = Just $ OpMod l
binAssignOpToOp (BinaryAssignAdd l) = Just $ OpAdd l
binAssignOpToOp (BinaryAssignSub l) = Just $ OpSub l
binAssignOpToOp (BinaryAssignAnd l) = Just $ OpBand l
binAssignOpToOp (BinaryAssignOr l)  = Just $ OpBor l
binAssignOpToOp (BinaryAssignXor l) = Just $ OpXor l

-- | typechecks an index condition
tcIndexCond :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcIndexCond e = tcExprTy (BaseT bool) e

-- | typechecks an index expression
tcIndexExpr :: (ProverK loc m) => IsVariadic -> Expression Identifier loc -> TcM m (SExpr VarIdentifier (Typed loc))
tcIndexExpr isVariadic e = do
    t <- if isVariadic
        then liftM (VAType (BaseT index)) $ newSizeVar Nothing
        else return (BaseT index)
    tcExprTy t e
    
tcExprTy :: (ProverK loc m) => Type -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    let Typed l ty' = loc e'
    x2 <- newTypedVar "ety" ty $ Just $ pp e
    tcTopCstrM l $ Coerces (fmap typed e') x2
    return $ fmap (Typed l) $ varExpr x2

tcSizes :: (ProverK loc m) => loc -> Type -> Sizes Identifier loc -> TcM m (Sizes VarIdentifier (Typed loc))
tcSizes l ty (Sizes szs) = do
    szs' <- mapM (\x -> tcVariadicArg (tcIndexExpr $ snd x) x) $ Foldable.toList szs
    -- check array's dimension
    tcCstrM l $ MatchTypeDimension ty $ map (mapFst (fmap typed)) szs'
    return $ Sizes $ fromListNe szs'

productIndexExpr :: (ProverK loc m) => loc -> (Expression VarIdentifier Type,IsVariadic) -> TcM m (Expression VarIdentifier Type)
productIndexExpr l (e,isVariadic) = do
    let product = mkVarId "product"
    (dec,[(x,_)]) <- tcTopPDecCstrM l True (Left product) Nothing [(e,isVariadic)] (BaseT index)
    return $ ProcCallExpr (BaseT index) (fmap (const $ DecT dec) $ ProcedureName () product) Nothing [(e,isVariadic)]

sumIndexExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)
sumIndexExprs l e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
sumIndexExprs l (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 + i2)
sumIndexExprs l e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ OpAdd $ NoType "sumIndexExprs") Nothing [(e1,False),(e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpAdd $ DecT dec) x2)

subtractIndexExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)
subtractIndexExprs l e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
subtractIndexExprs l (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 - i2)
subtractIndexExprs l e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ OpSub $ NoType "subtractIndexExprs") Nothing [(e1,False),(e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpSub $ DecT dec) x2)

multiplyIndexExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)
multiplyIndexExprs l e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
multiplyIndexExprs l (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 * i2)
multiplyIndexExprs l e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ OpMul $ NoType "multiplyIndexExprs") Nothing [(e1,False),(e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpMul $ DecT dec) x2)
    
landExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)
landExprs l e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ OpSub $ NoType "landExprs") Nothing [(e1,False),(e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpLand $ DecT dec) x2)

eqExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)
eqExprs l e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ OpEq $ NoType "eqExprs") Nothing [(e1,False),(e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpEq $ DecT dec) x2)
    
geExprs :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Expression VarIdentifier Type)
geExprs l e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- tcTopPDecCstrM l True (Right $ OpGe $ NoType "geExprs") Nothing [(e1,False),(e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpGe $ DecT dec) x2)
    







