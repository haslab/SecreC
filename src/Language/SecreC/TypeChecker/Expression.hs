{-# LANGUAGE ScopedTypeVariables, ViewPatterns, FlexibleContexts, DataKinds, TypeFamilies #-}

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
import Language.SecreC.TypeChecker.Conversion
import {-# SOURCE #-} Language.SecreC.Prover.Expression
import Language.SecreC.Prover.SMT
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.Vars
import Language.SecreC.Utils

import Prelude hiding (mapM)

import Control.Monad hiding (mapAndUnzipM,mapM)
import Control.Monad.IO.Class
import qualified Control.Monad.State as State

import Data.Bifunctor
import Data.Monoid hiding ((<>))
import Data.Either
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Int
import Data.Word
import qualified Data.Set as Set
import Data.Generics

import Text.PrettyPrint as PP

tcGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcGuard e = limitExprC ReadOnlyE $ tcExprTy (BaseT bool) e

tcAnnGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcAnnGuard e = limitExprC ReadOnlyE $ insideAnnotation $ do
    e' <- tcExpr e
    let (Typed l ty) = loc e'
    k <- newKindVar "k" False Nothing
    s <- newDomainTyVar "s" k Nothing
    topTcCstrM_ l $ Unifies ty (ComplexT $ CType s bool $ indexExpr 0)
    return e'

tcAnnExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcAnnExpr e = limitExprC ReadOnlyE $ insideAnnotation $ tcExpr e

tcLValue :: (ProverK loc m) => Bool -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcLValue isWrite (PostIndexExpr l e s) = do
    e' <- tcAddDeps l "lvalue" $ tcLValue isWrite e
    let t = typed $ loc e'
    (s',t') <- tcSubscript e' s
    return $ PostIndexExpr (Typed l t') e' s'
tcLValue isWrite (SelectionExpr l pe a) = do
    let va = bimap mkVarId id a
    pe' <- tcLValue isWrite pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    res <- newTyVar True Nothing
    topTcCstrM_ l $ ProjectStruct ctpe' (funit va) res
    return $ SelectionExpr (Typed l res) pe' (fmap (flip Typed res) va)
tcLValue isWrite (RVariablePExpr l v) = do
    v' <- tcVarName isWrite v
    let t = typed $ loc v'
    return $ RVariablePExpr (Typed l t) v'
tcLValue isWrite e = genTcError (locpos $ loc e) $ text "Not a l-value expression: " <+> quotes (pp e)

tcVariadicArg :: (PP (a VarIdentifier (Typed loc)),VarsIdTcM m,Located (a VarIdentifier (Typed loc)),Location loc,LocOf (a VarIdentifier (Typed loc)) ~ (Typed loc)) => (a Identifier loc -> TcM m (a VarIdentifier (Typed loc))) -> (a Identifier loc,IsVariadic) -> TcM m (a VarIdentifier (Typed loc),IsVariadic)
tcVariadicArg tcA (e,isVariadic) = do
    e' <- tcA e
    let (Typed l t) = loc e'
    if isVariadic
        then unless (isVATy t) $ genTcError (locpos l) $ text "Expression" <+> quotes (pp e' `ppOf` pp t) <+> text "should be variadic"
        else when (isVATy t) $ genTcError (locpos l) $ text "Expression" <+> quotes (pp e' `ppOf` pp t) <+> text "should not be variadic" 
    return (e',isVariadic)

tcPureExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcPureExpr e = withExprC PureE $ tcExpr e

tcExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcExpr (BinaryAssign l pe (binAssignOpToOp -> Just op) e) = do
    tcExpr $ BinaryAssign l pe (BinaryAssignEqual l) $ BinaryExpr l pe op e
tcExpr ae@(BinaryAssign l pe op@(BinaryAssignEqual ol) e) = do
    exprC <- getExprC
    when (exprC==PureE) $ genTcError (locpos l) $ text "assign expression is not pure" <+> pp ae
    pe' <- tcLValue True pe
    e' <- tcExpr e
    let tpe = typed $ loc pe'
    x1 <- newTypedVar "assign" tpe $ Just $ pp e'
    topTcCstrM_ l $ Coerces (fmap typed e') x1
    let ex1 = fmap (Typed l) $ RVariablePExpr tpe x1
    return $ BinaryAssign (Typed l tpe) pe' (fmap (notTyped "equal") op) ex1
tcExpr (QualExpr l e t) = do
    e' <- tcExpr e
    t' <- tcTypeSpec t False
    let ty = typed $ loc t'
    --x <- newTypedVar "qex" ty $ Just $ pp e' -- we add the size
    topTcCstrM_ l $ Unifies (typed $ loc e') ty
    return $ QualExpr (Typed l ty) e' t'
tcExpr (CondExpr l c e1 e2) = do
    (c',cstrsc) <- tcWithCstrs l "condexpr" $ tcGuard c
    e1' <- withDeps LocalScope $ do
        tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed c'
        limitExprC ReadOnlyE $ tcExpr e1
    e2' <- withDeps LocalScope $ do
        tryAddHypothesis l LocalScope cstrsc $ HypNotCondition $ fmap typed c'
        limitExprC ReadOnlyE $ tcExpr e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    t3 <- newTyVar False Nothing
    x1 <- newTypedVar "then" t3 $ Just $ pp e1'
    x2 <- newTypedVar "else" t3 $ Just $ pp e2'
    topTcCstrM_ l $ CoercesN [(fmap typed e1',x1),(fmap typed e2',x2)] 
    let ex1 = fmap (Typed l) $ varExpr x1
    let ex2 = fmap (Typed l) $ varExpr x2
    return $ CondExpr (Typed l t3) c' ex1 ex2
tcExpr (BinaryExpr l e1 op e2) = do
    e1' <- limitExprC ReadOnlyE $ tcExpr e1
    e2' <- limitExprC ReadOnlyE $ tcExpr e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    top <- tcOp op
    v <- newTyVar False Nothing
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l True True (Right $ fmap typed top) Nothing [(fmap typed e1',False),(fmap typed e2',False)] v
    return $ BinaryExpr (Typed l v) (fmap (Typed l) x1) (updLoc top (Typed l $ DecT dec)) (fmap (Typed l) x2)
tcExpr pe@(PreOp l op e) = do
    exprC <- getExprC
    when (exprC==PureE) $ genTcError (locpos l) $ text "preop is not pure" <+> pp pe
    e' <- tcLValue True e
    limitExprC ReadOnlyE $ tcBinaryOp l True op e'
tcExpr pe@(PostOp l op e) = do
    exprC <- getExprC
    when (exprC==PureE) $ genTcError (locpos l) $ text "postop is not pure" <+> pp pe
    e' <- tcLValue True e
    limitExprC ReadOnlyE $ tcBinaryOp l False op e'
tcExpr (UnaryExpr l op e) = do
    e' <- limitExprC ReadOnlyE $ tcExpr e
    let t = typed $ loc e'
    top <- tcOp op
    case (top,e) of
        -- hack to translate a literal cast to a qualified expression
        (OpCast lcast cast,e@(LitPExpr {})) -> do
            castty <- typeToBaseType (unTyped lcast) $ typed $ loc cast
            b <- typeBase l t
            topTcCstrM_ l $ Unifies b (BaseT castty)
        otherwise -> return ()
    
    v <- newTyVar False Nothing
    (dec,[(x,_)]) <- pDecCstrM l True True (Right $ fmap typed top) Nothing [(fmap typed e',False)] v
    let ex = fmap (Typed l) x
    return $ UnaryExpr (Typed l v) (updLoc top (Typed l $ DecT dec)) ex
tcExpr (DomainIdExpr l s) = do
    s' <- tcSecType s
    let t = BaseT index
    return $ DomainIdExpr (Typed l t) s'
tcExpr (StringFromBytesExpr l e) = do
    e' <- limitExprC ReadOnlyE $ tcExprTy (ComplexT bytes) e
    return $ StringFromBytesExpr (Typed l $ BaseT string) e'
tcExpr (BytesFromStringExpr l e) = do
    e' <- limitExprC ReadOnlyE $ tcExprTy (BaseT string) e
    return $ BytesFromStringExpr (Typed l $ ComplexT bytes) e'
tcExpr (VArraySizeExpr l e) = do
    e' <- limitExprC ReadOnlyE $ tcExpr e
    let t = typed $ loc e'
    unless (isVATy t) $ genTcError (locpos l) $ text "size... expects a variadic array but got" <+> quotes (pp e)
    return $ VArraySizeExpr (Typed l $ BaseT index) e'
tcExpr qe@(QuantifiedExpr l q vs e) = onlyAnn l (pp qe) $ tcLocal l "tcExpr quant" $ do
    q' <- tcQuantifier q
    vs' <- mapM tcQVar vs
    e' <- tcGuard e
    return $ QuantifiedExpr (Typed l $ BaseT bool) q' vs' e'
  where
    tcQVar (t,v) = do
        t' <- tcTypeSpec t False
        let ty = typed $ loc t'
        let v' = bimap mkVarId (flip Typed ty) v
        topTcCstrM_ l $ IsPublic True $ typed $ loc v'
        isAnn <- getAnn
        newVariable LocalScope True isAnn v' Nothing -- don't add values to the environment
        return (t',v')
tcExpr le@(LeakExpr l e) = onlyLeak l (pp le) $ onlyAnn l (pp le) $ do
    e' <- limitExprC ReadOnlyE $ tcExpr e
    topTcCstrM_ l $ IsPrivate True $ typed $ loc e'
    return $ LeakExpr (Typed l $ BaseT bool) e'
tcExpr call@(ProcCallExpr l n@(ProcedureName pl pn) specs es) = do
    let vn = bimap mkVarId id n
    specs' <- mapM (mapM (tcVariadicArg tcTemplateTypeArgument)) specs
    es' <- limitExprC ReadOnlyE $ mapM (tcVariadicArg tcExpr) es
    let tspecs = fmap (map (mapFst (typed . loc))) specs'
    v <- newTyVar False Nothing
    (dec,xs) <- pDecCstrM l True True (Left $ procedureNameId vn) tspecs (map (mapFst (fmap typed)) es') v
    let exs = map (mapFst (fmap (Typed l))) xs
    return $ ProcCallExpr (Typed l v) (fmap (flip Typed (DecT dec)) vn) specs' exs
tcExpr (PostIndexExpr l e s) = limitExprC ReadOnlyE $ do
    e' <- tcAddDeps l "postindex" $ tcExpr e
    let t = typed $ loc e'
    (s',t') <- tcSubscript e' s
    return $ PostIndexExpr (Typed l t') e' s'
tcExpr (SelectionExpr l pe a) = limitExprC ReadOnlyE $ do
    let va = bimap mkVarId id a
    pe' <- tcExpr pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    tres <- newTyVar True Nothing
    topTcCstrM_ l $ ProjectStruct ctpe' (funit va) tres
    return $ SelectionExpr (Typed l tres) pe' (fmap (flip Typed tres) va)
tcExpr (ArrayConstructorPExpr l es) = limitExprC ReadOnlyE $ do
    lit' <- tcArrayLiteral l es
    return lit'
tcExpr e@(MultisetConstructorPExpr l es) = limitExprC ReadOnlyE $ onlyAnn l (pp e) $ do
    lit' <- tcMultisetLiteral l es
    return lit'
tcExpr (LitPExpr l lit) = limitExprC ReadOnlyE $ do
    lit' <- tcLiteral lit
    return lit'
tcExpr (RVariablePExpr l v) = do
    v' <- tcVarName False v
    let t = typed $ loc v'
    return $ RVariablePExpr (Typed l t) v'
tcExpr (BuiltinExpr l n args) = do
    args' <- limitExprC ReadOnlyE $ mapM tcExpr args
    ret <- isSupportedBuiltin l n $ map (typed . loc) args'
    return $ BuiltinExpr (Typed l ret) n args'
tcExpr me@(ToMultisetExpr l e) = limitExprC ReadOnlyE $ onlyAnn l (pp me) $ do
    e' <- tcExpr e
    ComplexT mset <- newTyVar True Nothing
    topTcCstrM_ l $ ToMultiset (typed $ loc e') mset
    return $ ToMultisetExpr (Typed l $ ComplexT mset) e'
tcExpr e@(ResultExpr l) = limitExprC ReadOnlyE $ onlyAnn l (pp e) $ do
    VarName tl _ <- checkVariable False False True LocalScope $ VarName l $ mkVarId "\\result"
    return $ ResultExpr tl
tcExpr e = genTcError (locpos $ loc e) $ text "failed to typecheck expression" <+> pp e

isSupportedBuiltin :: (MonadIO m,Location loc) => loc -> Identifier -> [Type] -> TcM m Type
isSupportedBuiltin l n args = do -- TODO: check specific builtins?
    ret <- newTyVar True Nothing
    return ret

stmtsReturnExprs :: (Data iden,Data loc) => [Statement iden loc] -> [Expression iden loc]
stmtsReturnExprs ss = concatMap stmtReturnExprs ss
stmtReturnExprs :: (Data iden,Data loc) => Statement iden loc -> [Expression iden loc]
stmtReturnExprs (ReturnStatement _ e) = maybeToList e
stmtReturnExprs s = gmapQr (++) [] (mkQ [] stmtsReturnExprs `extQ` stmtReturnExprs) s

tcQuantifier :: ProverK loc m => Quantifier loc -> TcM m (Quantifier (Typed loc))
tcQuantifier (ForallQ l) = return $ ForallQ (notTyped "quantifier" l)
tcQuantifier (ExistsQ l) = return $ ExistsQ (notTyped "quantifier" l)
    
tcBinaryOp :: (ProverK loc m) => loc -> Bool -> Op Identifier loc -> Expression VarIdentifier (Typed loc) -> TcM m (Expression VarIdentifier (Typed loc))
tcBinaryOp l isPre op e1 = do
    elit1 <- tcLiteral $ IntLit l 1
    top <- tcOp op
    let t1 = typed $ loc e1
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l True True (Right $ fmap typed top) Nothing [(fmap typed e1,False),(fmap typed elit1,False)] t1
    let ex1 = fmap (Typed l) x1
    let op' = updLoc top (Typed l $ DecT dec)
    let t' = typed $ loc ex1
    let cons = if isPre then PreOp else PostOp
    return $ cons (Typed l t') op' ex1    

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
    ret <- newTyVar False Nothing
    withDependencies ks $ topTcCstrM_ l $ ProjectMatrix t (Foldable.toList rngs) ret
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
    b <- newBaseTyVar Nothing
    let t = BaseT b
    let elit = LitPExpr t $ fmap (const t) li
    topTcCstrM_ l $ CoercesLit elit
    return $ LitPExpr (Typed l t) $ fmap (const (Typed l t)) li

tcArrayLiteral :: (ProverK loc m) => loc -> [Expression Identifier loc] -> TcM m (Expression VarIdentifier (Typed loc))
tcArrayLiteral l es = do
    es' <- mapM tcExpr es
    let es'' = fmap (fmap typed) es'
    k <- newKindVar "k" False Nothing
    s <- newDomainTyVar "s" k Nothing
    b <- newBaseTyVar Nothing
    let t = ComplexT $ CType s b (indexExpr 1)
    let elit = ArrayConstructorPExpr t es''
    topTcCstrM_ l $ CoercesLit elit
    return $ ArrayConstructorPExpr (Typed l t) es'

tcMultisetLiteral :: (ProverK loc m) => loc -> [Expression Identifier loc] -> TcM m (Expression VarIdentifier (Typed loc))
tcMultisetLiteral l es = do
    es' <- mapM tcExpr es
    let es'' = fmap (fmap typed) es'
    k <- newKindVar "k" False Nothing
    s <- newDomainTyVar "s" k Nothing
    b <- newBaseTyVar Nothing
    let t = ComplexT $ CType s (MSet b) (indexExpr 0)
    let elit = MultisetConstructorPExpr t es''
    topTcCstrM_ l $ CoercesLit elit
    return $ MultisetConstructorPExpr (Typed l t) es'

tcVarName :: (ProverK loc m) => Bool -> VarName Identifier loc -> TcM m (VarName VarIdentifier (Typed loc))
tcVarName isWrite v@(VarName l n) = do
    exprC <- getExprC
    isAnn <- getAnn
    checkVariable isWrite (exprC==PureE) isAnn LocalScope (bimap mkVarId id v)

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
tcIndexExpr :: (ProverK loc m) => IsVariadic -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcIndexExpr isVariadic e = do
    t <- if isVariadic
        then liftM (VAType (BaseT index)) $ newSizeVar Nothing
        else return (BaseT index)
    tcExprTy t e
    
tcExprTy :: (ProverK loc m) => Type -> Expression Identifier loc -> TcM m (Expression VarIdentifier (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    tcExprTy' ty e'
    
tcExprTy' :: (ProverK loc m) => Type -> Expression VarIdentifier (Typed loc) -> TcM m (Expression VarIdentifier (Typed loc))
tcExprTy' ty e' = do
    let Typed l ty' = loc e'
    x2 <- newTypedVar "ety" ty $ Just $ pp e'
    topTcCstrM_ l $ Coerces (fmap typed e') x2
    return $ fmap (Typed l) $ varExpr x2

tcSizes :: (ProverK loc m) => loc -> Sizes Identifier loc -> TcM m (Sizes VarIdentifier (Typed loc))
tcSizes l (Sizes szs) = do
    szs' <- mapM (\x -> tcVariadicArg (tcIndexExpr $ snd x) x) $ Foldable.toList szs
    -- check array's dimension
    --tcCstrM l $ MatchTypeDimension ty $ map (mapFst (fmap typed)) szs'
    return $ Sizes $ fromListNe szs'

repeatExpr :: ProverK loc m => loc -> Bool -> Expr -> Maybe Expr -> ComplexType -> TcM m Expr
repeatExpr l isTop e Nothing t = do
    let repeat = mkVarId "repeat"
    (dec,es') <- pDecCstrM l isTop False (Left repeat) Nothing [(e,False)] (ComplexT t)
    return $ ProcCallExpr (ComplexT t) (fmap (const $ DecT dec) $ ProcedureName () repeat) Nothing es'
repeatExpr l isTop e (Just sz) t = do
    let repeat = mkVarId "repeat"
    (dec,es') <- pDecCstrM l isTop False (Left repeat) Nothing [(e,False),(sz,False)] (ComplexT t)
    return $ ProcCallExpr (ComplexT t) (fmap (const $ DecT dec) $ ProcedureName () repeat) Nothing es'

classifyExpr :: ProverK loc m => loc -> Bool -> Expr -> ComplexType -> TcM m Expr
classifyExpr l isTop e t = do
    let classify = mkVarId "classify"
    (dec,es') <- pDecCstrM l isTop False (Left classify) Nothing [(e,False)] (ComplexT t)
    return $ ProcCallExpr (ComplexT t) (fmap (const $ DecT dec) $ ProcedureName () classify) Nothing es'

shapeExpr :: ProverK loc m => loc -> Bool -> Expr -> TcM m Expr
shapeExpr l isTop e = do
    let shape = mkVarId "shape"
    let indexes = ComplexT $ CType Public index (indexExpr 1)
    (dec,es') <- pDecCstrM l isTop False (Left shape) Nothing [(e,False)] indexes
    return $ ProcCallExpr indexes (fmap (const $ DecT dec) $ ProcedureName () shape) Nothing es'

reshapeExpr :: ProverK loc m => loc -> Bool -> Expr -> [(Expr,IsVariadic)] -> Type -> TcM m Expr
reshapeExpr l isTop e ns ret = do
    let reshape = mkVarId "reshape"
    (dec,ns') <- pDecCstrM l isTop False (Left reshape) Nothing ((e,False):ns) ret
    return $ ProcCallExpr ret (fmap (const $ DecT dec) $ ProcedureName () reshape) Nothing ns'

productIndexExpr :: (ProverK loc m) => loc -> Bool -> (Expr,IsVariadic) -> TcM m Expr
productIndexExpr l isTop (e,isVariadic) = do
    let product = mkVarId "product"
    (dec,es') <- pDecCstrM l isTop True (Left product) Nothing [(e,isVariadic)] (BaseT index)
    return $ ProcCallExpr (BaseT index) (fmap (const $ DecT dec) $ ProcedureName () product) Nothing es'

sumIndexExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
sumIndexExprs l isTop e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
sumIndexExprs l isTop (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 + i2)
sumIndexExprs l isTop e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l isTop True (Right $ OpAdd $ NoType "sumIndexExprs") Nothing [(e1,False),(e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpAdd $ DecT dec) x2)

subtractIndexExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
subtractIndexExprs l isTop e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
subtractIndexExprs l isTop (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 - i2)
subtractIndexExprs l isTop e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l isTop True (Right $ OpSub $ NoType "subtractIndexExprs") Nothing [(e1,False),(e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpSub $ DecT dec) x2)

multiplyIndexExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
multiplyIndexExprs l isTop e1 e2@(LitPExpr _ (IntLit _ 1)) = return e1
multiplyIndexExprs l isTop (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 * i2)
multiplyIndexExprs l isTop e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l isTop True (Right $ OpMul $ NoType "multiplyIndexExprs") Nothing [(e1,False),(e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpMul $ DecT dec) x2)

multiplyIndexVariadicExprs :: (ProverK loc m) => loc -> Bool -> [(Expr,IsVariadic)] -> TcM m Expr
multiplyIndexVariadicExprs l isTop es = do
    es' <- liftM concat $ mapM (expandVariadicExpr l) es
    multiplyIndexVariadicExprs' l es'
  where
    multiplyIndexVariadicExprs' :: (ProverK loc m) => loc -> [Expr] -> TcM m Expr
    multiplyIndexVariadicExprs' l [] = return $ indexExpr 0
    multiplyIndexVariadicExprs' l [e] = return e
    multiplyIndexVariadicExprs' l (e:es) = do
        es' <- multiplyIndexVariadicExprs' l es
        multiplyIndexExprs l isTop e es'

landExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
landExprs l isTop e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l isTop True (Right $ OpSub $ NoType "landExprs") Nothing [(e1,False),(e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpLand $ DecT dec) x2)

allExprs :: ProverK loc m => loc -> Bool -> [Expr] -> TcM m Expr
allExprs l isTop [] = return $ trueExpr
allExprs l isTop es = foldr1M (landExprs l isTop) es

eqExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
eqExprs l isTop e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l isTop True (Right $ OpEq $ NoType "eqExprs") Nothing [(e1,False),(e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpEq $ DecT dec) x2)
    
geExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
geExprs l isTop e1 e2 = do
    (dec,[(x1,_),(x2,_)]) <- pDecCstrM l isTop True (Right $ OpGe $ NoType "geExprs") Nothing [(e1,False),(e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpGe $ DecT dec) x2)
    
negBoolExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc)
negBoolExprLoc e = BuiltinExpr (Typed noloc $ BaseT bool) "core.eq" [e,fmap (Typed noloc) $ falseExpr]

impliesExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)
impliesExprLoc e1 e2 = BuiltinExpr (Typed noloc $ BaseT bool) "core.implies" [e1,e2]

andExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)
andExprLoc e1 e2 = BuiltinExpr (Typed noloc $ BaseT bool) "core.band" [e1,e2]

andExprsLoc :: Location loc => [Expression iden (Typed loc)] -> Expression iden (Typed loc)
andExprsLoc [] = fmap (Typed noloc) trueExpr
andExprsLoc [e] = e
andExprsLoc (e:es) = andExprLoc e (andExprsLoc es)






