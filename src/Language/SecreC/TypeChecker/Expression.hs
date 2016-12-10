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

tcGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcGuard e = limitExprC ReadOnlyExpr $ tcExprTy (BaseT bool) e

tcBoolExpr :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcBoolExpr e = limitExprC ReadOnlyExpr $ do
    let l = loc e
    k <- newKindVar "k" Nothing False Nothing
    s <- newDomainTyVar "s" k False Nothing
    let ret = ComplexT $ CType s bool $ indexExpr 0
    e' <- tcExpr (Just ret) e
    return e'

tcAnnGuard :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcAnnGuard e = limitExprC ReadOnlyExpr $ insideAnnotation $ do
    let ret = ComplexT $ CType Public bool $ indexExpr 0
    e' <- tcExpr (Just ret) e
    let (Typed l ty) = loc e'
--    k <- newKindVar "k" Nothing False Nothing
--    s <- newDomainTyVar "s" k False Nothing
    return e'

tcAnnExpr :: (ProverK loc m) => Maybe Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcAnnExpr ret e = limitExprC ReadOnlyExpr $ insideAnnotation $ tcExpr ret e

tcLValue :: (ProverK loc m) => Bool -> Maybe Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcLValue isWrite ret (PostIndexExpr l e s) = do
    e' <- tcAddDeps l "lvalue" $ tcLValue isWrite Nothing e
    let t = typed $ loc e'
    (s',t') <- tcSubscript ret e' s
    return $ PostIndexExpr (Typed l t') e' s'
tcLValue isWrite ret (SelectionExpr l pe a) = do
    res <- newTyVar True False Nothing
    unifiesRet l ret res
    
    let va = bimap (TIden . mkVarId) id a
    pe' <- tcLValue isWrite Nothing pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    topTcCstrM_ l $ ProjectStruct ctpe' (funit va) res
    return $ SelectionExpr (Typed l res) pe' (fmap (flip Typed res) va)
tcLValue isWrite ret (RVariablePExpr l v) = do
    v' <- tcVarName isWrite v
    let t = typed $ loc v'
    unifiesRet l ret t
    return $ RVariablePExpr (Typed l t) v'
tcLValue isWrite ret e = do
    ppe <- pp e
    genTcError (locpos $ loc e) False $ text "Not a l-value expression: " <+> quotes ppe

tcVariadicArg :: (PP (TcM m) (a GIdentifier (Typed loc)),VarsGTcM m,Located (a GIdentifier (Typed loc)),Location loc,LocOf (a GIdentifier (Typed loc)) ~ (Typed loc)) => (a Identifier loc -> TcM m (a GIdentifier (Typed loc))) -> (a Identifier loc,IsVariadic) -> TcM m (a GIdentifier (Typed loc),IsVariadic)
tcVariadicArg tcA (e,isVariadic) = do
    e' <- tcA e
    let (Typed l t) = loc e'
    ppe' <- pp e'
    ppt <- pp t
    if isVariadic
        then unless (isVATy t) $ genTcError (locpos l) False $ text "Expression" <+> quotes (ppe' `ppOf` ppt) <+> text "should be variadic"
        else when (isVATy t) $ genTcError (locpos l) False $ text "Expression" <+> quotes (ppe' `ppOf` ppt) <+> text "should not be variadic" 
    return (e',isVariadic)

tcPureExpr :: (ProverK loc m) => Maybe Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcPureExpr ret e = withExprC PureExpr $ tcExpr ret e

unifiesRet :: ProverK loc m => loc -> Maybe Type -> Type -> TcM m ()
unifiesRet l Nothing t = return ()
unifiesRet l (Just ret) t = topTcCstrM_ l $ Unifies ret t

mkRet :: ProverK loc m => loc -> Bool -> Bool -> Maybe Type -> TcM m Type
mkRet l isNotVoid isVariadic (Just t) = return t
mkRet l isNotVoid isVariadic Nothing = newTyVar isNotVoid isVariadic Nothing

tcExpr :: (ProverK loc m) => Maybe Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcExpr ret (BinaryAssign l pe (binAssignOpToOp -> Just op) e) = do
    tcExpr ret $ BinaryAssign l pe (BinaryAssignEqual l) $ BinaryExpr l pe op e
tcExpr ret ae@(BinaryAssign l pe op@(BinaryAssignEqual ol) e) = do
    exprC <- getExprC
    when (exprC==PureExpr) $ do
        ppae <- pp ae
        genTcError (locpos l) False $ text "assign expression is not pure" <+> ppae
    pe' <- tcLValue True Nothing pe
    e' <- tcExpr Nothing e
    let tpe = typed $ loc pe'
    ppe' <- pp e'
    x1 <- tcCoerces l True Nothing (fmap typed e') tpe
    let ex1 = fmap (Typed l) x1
    unifiesRet l ret tpe
    return $ BinaryAssign (Typed l tpe) pe' (fmap (notTyped "equal") op) ex1
tcExpr ret (QualExpr l e t) = do
    t' <- tcTypeSpec t False False
    let ty = typed $ loc t'
    --x <- newTypedVar "qex" ty $ Just $ pp e' -- we add the size
    unifiesRet l ret ty
    e' <- tcExpr (Just ty) e
    topTcCstrM_ l $ Unifies (typed $ loc e') ty
    return $ QualExpr (Typed l ty) e' t'
tcExpr ret (CondExpr l c e1 e2) = do
    (c',cstrsc) <- tcWithCstrs l "condexpr" $ tcGuard c
    e1' <- withDeps LocalScope $ do
        tryAddHypothesis l "tcExpr cond then" LocalScope checkAssertions cstrsc $ HypCondition $ fmap typed c'
        limitExprC ReadOnlyExpr $ tcExpr Nothing e1
    e2' <- withDeps LocalScope $ do
        tryAddHypothesis l "tcExpr cond else" LocalScope checkAssertions cstrsc $ HypNotCondition $ fmap typed c'
        limitExprC ReadOnlyExpr $ tcExpr Nothing e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    ppe1' <- pp e1'
    ppe2' <- pp e2'
    t3 <- mkRet l True False ret
    [x1,x2] <- tcCoercesN l True [fmap typed e1',fmap typed e2'] t3
    let ex1 = fmap (Typed l) x1
    let ex2 = fmap (Typed l) x2
    return $ CondExpr (Typed l t3) c' ex1 ex2
tcExpr ret (BinaryExpr l e1 op e2) = do
    e1' <- limitExprC ReadOnlyExpr $ tcExpr Nothing e1
    e2' <- limitExprC ReadOnlyExpr $ tcExpr Nothing e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    top <- tcOp op
    v <- mkRet l True False ret
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing True False True (OIden $ fmap typed top) Nothing [(False,Left $ fmap typed e1',False),(False,Left $ fmap typed e2',False)] v
    return $ BinaryExpr (Typed l v) (fmap (Typed l) x1) (updLoc top (Typed l $ DecT dec)) (fmap (Typed l) x2)
tcExpr ret pe@(PreOp l op e) = do
    exprC <- getExprC
    when (exprC==PureExpr) $ do
        pppe <- pp pe
        genTcError (locpos l) False $ text "preop is not pure" <+> pppe
    e' <- tcLValue True ret e
    limitExprC ReadOnlyExpr $ tcPrePostOp l True op e'
tcExpr ret pe@(PostOp l op e) = do
    exprC <- getExprC
    when (exprC==PureExpr) $ do
        pppe <- pp pe
        genTcError (locpos l) False $ text "postop is not pure" <+> pppe
    e' <- tcLValue True ret e
    limitExprC ReadOnlyExpr $ tcPrePostOp l False op e'
tcExpr ret (UnaryExpr l op e) = do
    e' <- limitExprC ReadOnlyExpr $ tcExpr Nothing e
    let t = typed $ loc e'
    top <- tcOp op
    case (top,e) of
        -- hack to translate a literal cast to a qualified expression
        (OpCast lcast cast,e@(LitPExpr {})) -> do
            castty <- typeToBaseType (unTyped lcast) $ typed $ loc cast
            b <- typeBase l t
            topTcCstrM_ l $ Unifies b (BaseT castty)
        otherwise -> return ()
    v <- mkRet l True False ret
    (dec,[(_,Left x,_)]) <- pDecCstrM l Nothing True False True (OIden $ fmap typed top) Nothing [(False,Left $ fmap typed e',False)] v
    let ex = fmap (Typed l) x
    return $ UnaryExpr (Typed l v) (updLoc top (Typed l $ DecT dec)) ex
tcExpr ret (DomainIdExpr l s) = do
    let t = BaseT index
    unifiesRet l ret t
    s' <- tcSecType s
    return $ DomainIdExpr (Typed l t) s'
tcExpr ret (StringFromBytesExpr l e) = do
    let t = BaseT string
    unifiesRet l ret t
    e' <- limitExprC ReadOnlyExpr $ tcExprTy (ComplexT bytes) e
    return $ StringFromBytesExpr (Typed l t) e'
tcExpr ret (BytesFromStringExpr l e) = do
    let t = ComplexT bytes
    unifiesRet l ret t
    e' <- limitExprC ReadOnlyExpr $ tcExprTy (BaseT string) e
    return $ BytesFromStringExpr (Typed l t) e'
tcExpr ret (VArraySizeExpr l e) = do
    let bt = BaseT index
    unifiesRet l ret bt
    e' <- withExprC ReadOnlyExpr $ tcExpr Nothing e
    let t = typed $ loc e'
    unless (isVATy t) $ do
        ppe <- pp e
        genTcError (locpos l) False $ text "size... expects a variadic array but got" <+> quotes ppe
    return $ VArraySizeExpr (Typed l bt) e'
tcExpr ret qe@(QuantifiedExpr l q vs e) = do
    ppqe <- pp qe
    onlyAnn l ppqe $ tcLocal l "tcExpr quant" $ do
        q' <- tcQuantifier q
        vs' <- mapM (tcQVar l) vs
        e' <- tcGuard e
        let te = typed $ loc e'
        unifiesRet l ret te
        return $ QuantifiedExpr (Typed l te) q' vs' e'
tcExpr ret le@(LeakExpr l e) = do
    pple <- pp le
    onlyLeak l (pple) $ onlyAnn l (pple) $ do
        let t = BaseT bool
        unifiesRet l ret t
        e' <- limitExprC ReadOnlyExpr $ tcExpr Nothing e
        topTcCstrM_ l $ IsPrivate True $ typed $ loc e'
        return $ LeakExpr (Typed l t) e'
tcExpr ret call@(ProcCallExpr l n@(ProcedureName pl pn) specs es) = do
    let vn = bimap (mkVarId) id n
    specs' <- mapM (mapM (tcVariadicArg tcTemplateTypeArgument)) specs
    es' <- limitExprC ReadOnlyExpr $ mapM (tcVariadicArg (tcExpr Nothing)) es
    let tspecs = fmap (map (mapFst (typed . loc))) specs'
    v <- mkRet l False False ret
    (dec,xs) <- pDecCstrM l Nothing True False True (PIden $ procedureNameId vn) tspecs (map (\(x,y) -> (False,Left $ fmap typed x,y)) es') v
    let exs = map (\(x,Left y,z) -> (fmap (Typed l) y,z)) xs
    return $ ProcCallExpr (Typed l v) (bimap PIden (flip Typed (DecT dec)) vn) specs' exs
tcExpr ret (PostIndexExpr l e s) = limitExprC ReadOnlyExpr $ do
    e' <- tcAddDeps l "postindex" $ tcExpr Nothing e
    let t = typed $ loc e'
    (s',t') <- tcSubscript ret e' s
    return $ PostIndexExpr (Typed l t') e' s'
tcExpr ret (SelectionExpr l pe a) = limitExprC ReadOnlyExpr $ do
    let va = bimap (TIden . mkVarId) id a -- marking attributes as types
    pe' <- tcExpr Nothing pe
    let tpe' = typed $ loc pe'
    ctpe' <- typeToBaseType l tpe'
    tres <- mkRet l True False ret
    topTcCstrM_ l $ ProjectStruct ctpe' (funit va) tres
    return $ SelectionExpr (Typed l tres) pe' (fmap (flip Typed tres) va)
tcExpr ret (ArrayConstructorPExpr l es) = limitExprC ReadOnlyExpr $ do
    lit' <- tcArrayLiteral l ret es
    return lit'
tcExpr ret e@(MultisetConstructorPExpr l es) = do
    ppe <- pp e
    limitExprC ReadOnlyExpr $ onlyAnn l (ppe) $ do
        lit' <- tcMultisetLiteral l ret es
        return lit'
tcExpr ret e@(SetConstructorPExpr l es) = do
    ppe <- pp e
    limitExprC ReadOnlyExpr $ onlyAnn l (ppe) $ do
        lit' <- tcSetLiteral l ret es
        return lit'
tcExpr ret (LitPExpr l lit) = limitExprC ReadOnlyExpr $ do
    lit' <- tcLiteral ret lit
    return lit'
tcExpr ret (RVariablePExpr l v) = do
    v' <- tcVarName False v
    let t = typed $ loc v'
    unifiesRet l ret t
    return $ RVariablePExpr (Typed l t) v'
tcExpr ret (BuiltinExpr l n args) = do
    args' <- limitExprC ReadOnlyExpr $ mapM (tcVariadicArg (tcExpr Nothing)) args
    tret <- isSupportedBuiltin l n $ map (typed . loc . fst) args'
    unifiesRet l ret tret
    return $ BuiltinExpr (Typed l tret) n args'
tcExpr ret me@(ToMultisetExpr l e) = do
    ppme <- pp me
    limitExprC ReadOnlyExpr $ onlyAnn l (ppme) $ do
        mset <- newBaseTyVar Nothing False Nothing
        unifiesRet l ret $ BaseT mset
        
        e' <- tcExpr Nothing e
        topTcCstrM_ l $ ToMultiset (typed $ loc e') mset
        return $ ToMultisetExpr (Typed l $ BaseT mset) e'
tcExpr ret me@(ToSetExpr l e) = do
    ppme <- pp me
    limitExprC ReadOnlyExpr $ onlyAnn l (ppme) $ do
        set <- newBaseTyVar Nothing False Nothing
        unifiesRet l ret $ BaseT set
        
        e' <- tcExpr Nothing e
        topTcCstrM_ l $ ToSet (Right $ typed $ loc e') set
        return $ ToSetExpr (Typed l $ BaseT set) e'
tcExpr ret me@(SetComprehensionExpr l t x px fx) = do
    ppme <- pp me
    limitExprC ReadOnlyExpr $ onlyAnn l (ppme) $ tcLocal l "set comprehension" $ do
        set <- newBaseTyVar Nothing False Nothing
        unifiesRet l ret $ BaseT set
        
        (t',x') <- tcQVar l (t,x)
        px' <- tcGuard px
        fx' <- mapM (tcExpr Nothing) fx
        let setb = maybe (typed $ loc t') (typed . loc) fx'
        topTcCstrM_ l $ ToSet (Left setb) set
        return $ SetComprehensionExpr (Typed l $ BaseT set) t' x' px' fx'
tcExpr ret me@(ToVArrayExpr l e i) = limitExprC ReadOnlyExpr $ do
    k <- newKindVar "k" Nothing False Nothing
    s <- newDomainTyVar "s" k False Nothing
    b <- newBaseTyVar Nothing False Nothing
    sz <- newSizeVar False Nothing
    let varr = VAType (ComplexT $ CType s b $ indexExpr 0) sz
    unifiesRet l ret varr
    
    x' <- tcExprTy (ComplexT $ CType s b $ indexExpr 1) e
    i' <- tcIndexExpr False i
    topTcCstrM_ l $ Unifies (IdxT $ fmap typed i') (IdxT sz)
    return $ ToVArrayExpr (Typed l varr) (x') i'
tcExpr ret e@(ResultExpr l) = do
    ppe <- pp e
    limitExprC ReadOnlyExpr $ onlyAnn l (ppe) $ do
        VarName tl _ <- checkVariable False False True LocalScope $ VarName l $ mkVarId "\\result"
        unifiesRet l ret $ typed tl
        return $ ResultExpr tl
tcExpr ret e = do
    ppe <- pp e
    genTcError (locpos $ loc e) False $ text "failed to typecheck expression" <+> ppe

tcQVar :: ProverK loc m => loc -> (TypeSpecifier Identifier loc,VarName Identifier loc) -> TcM m (TypeSpecifier GIdentifier (Typed loc),VarName GIdentifier (Typed loc))
tcQVar l (t,v) = do
    t' <- tcTypeSpec t False False
    let ty = typed $ loc t'
    let v' = bimap (VIden . mkVarId) (flip Typed ty) v
    topTcCstrM_ l $ IsPublic True $ typed $ loc v'
    isAnn <- getAnn
    newVariable LocalScope True isAnn v' Nothing -- don't add values to the environment
    return (t',v')

isSupportedBuiltin :: (MonadIO m,Location loc) => loc -> Identifier -> [Type] -> TcM m Type
isSupportedBuiltin l n args = do -- TODO: check specific builtins?
    ret <- newTyVar True False Nothing
    return ret

stmtsReturnExprs :: (Data iden,Data loc) => [Statement iden loc] -> [Expression iden loc]
stmtsReturnExprs ss = concatMap stmtReturnExprs ss
stmtReturnExprs :: (Data iden,Data loc) => Statement iden loc -> [Expression iden loc]
stmtReturnExprs (ReturnStatement _ e) = maybeToList e
stmtReturnExprs s = gmapQr (++) [] (mkQ [] stmtsReturnExprs `extQ` stmtReturnExprs) s

tcQuantifier :: ProverK loc m => Quantifier loc -> TcM m (Quantifier (Typed loc))
tcQuantifier (ForallQ l) = return $ ForallQ (notTyped "quantifier" l)
tcQuantifier (ExistsQ l) = return $ ExistsQ (notTyped "quantifier" l)
    
tcPrePostOp :: (ProverK loc m) => loc -> Bool -> Op Identifier loc -> Expression GIdentifier (Typed loc) -> TcM m (Expression GIdentifier (Typed loc))
tcPrePostOp l isPre op e1 = do
    elit1 <- tcLiteral Nothing $ IntLit l 1
    top <- tcOp op
    let t1 = typed $ loc e1
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing True False True (OIden $ fmap typed top) Nothing [(False,Left $ fmap typed e1,False),(False,Left $ fmap typed elit1,False)] t1
    let ex1 = fmap (Typed l) x1
    let op' = updLoc top (Typed l $ DecT dec)
    let t' = typed $ loc ex1
    let cons = if isPre then PreOp else PostOp
    return $ cons (Typed l t') op' ex1    

tcOp :: (ProverK loc m) => Op Identifier loc -> TcM m (Op GIdentifier (Typed loc))
tcOp (OpCast l t) = do
    t' <- tcCastType t
    return $ OpCast (notTyped "tcOp" l) t'
tcOp op = return $ bimap (PIden . mkVarId) (notTyped "tcOp") op

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: (ProverK loc m) => Maybe Type -> Expression GIdentifier (Typed loc) -> Subscript Identifier loc -> TcM m (Subscript GIdentifier (Typed loc),Type)
tcSubscript ret e s = do
    let t = typed $ loc e
    let l = loc s
    ((s',rngs),ks) <- tcWithCstrs l "subscript" $ mapAndUnzipM tcIndex s
    ret' <- case t of
        VAType t _ -> case indexProjs (Foldable.toList s) of
            0 -> mkVariadicTyArray True False t
            otherwise -> newTyVar True False Nothing
        otherwise -> newTyVar True False Nothing
    unifiesRet l ret ret'
    withDependencies ks $ topTcCstrM_ l $ ProjectMatrix t (Foldable.toList rngs) ret'
    return (s',ret')

indexProjs :: [Index iden loc] -> Word64
indexProjs [] = 0
indexProjs (IndexInt {}:xs) = 1 + indexProjs xs
indexProjs (IndexSlice {}:xs) = indexProjs xs

tcIndex :: (ProverK loc m) => Index Identifier loc -> TcM m (Index GIdentifier (Typed loc),ArrayProj)
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

tcLiteral :: (ProverK loc m) => Maybe Type -> Literal loc -> TcM m (Expression GIdentifier (Typed loc))
tcLiteral ret li = do
    let l = loc li
    b <- newBaseTyVar Nothing False Nothing
    let t = BaseT b
    unifiesRet l ret t
    
    let elit = LitPExpr t $ fmap (const t) li
    topTcCstrM_ l $ CoercesLit elit
    opts <- askOpts
    return $ fmap (Typed l) elit

tcArrayLiteral :: (ProverK loc m) => loc -> Maybe Type -> [Expression Identifier loc] -> TcM m (Expression GIdentifier (Typed loc))
tcArrayLiteral l ret es = do
    s <- do
        k <- newKindVar "k" Nothing False Nothing
        s <- newDomainTyVar "s" k False Nothing
        return s
    b <- newBaseTyVar Nothing False Nothing
    let t = ComplexT $ CType s b (indexExpr 1)
    let bt = ComplexT $ CType s b (indexExpr 0)
    unifiesRet l ret t
    
    opts <- askOpts
    es' <- mapM (tcExpr $ Just bt) es
    let es'' = fmap (fmap typed) es'
    xs <- tcCoercesN l True es'' bt
    return $ ArrayConstructorPExpr (Typed l t) $ map (fmap (Typed l)) xs

tcMultisetLiteral :: (ProverK loc m) => loc -> Maybe Type -> [Expression Identifier loc] -> TcM m (Expression GIdentifier (Typed loc))
tcMultisetLiteral l ret es = do
    ct@(ComplexT bt) <- newTyVar False False Nothing
    let t = BaseT (MSet bt)
    unifiesRet l ret t
    
    es' <- mapM (tcExpr $ Just ct) es
    let es'' = fmap (fmap typed) es'
    xs <- tcCoercesN l True es'' ct
    return $ MultisetConstructorPExpr (Typed l t) $ map (fmap (Typed l)) xs

tcSetLiteral :: (ProverK loc m) => loc -> Maybe Type -> [Expression Identifier loc] -> TcM m (Expression GIdentifier (Typed loc))
tcSetLiteral l ret es = do
    ct@(ComplexT bt) <- newTyVar False False Nothing
    let t = BaseT $ Set bt
    unifiesRet l ret t
    
    es' <- mapM (tcExpr $ Just ct) es
    let es'' = fmap (fmap typed) es'
    xs <- tcCoercesN l True es'' ct
    return $ SetConstructorPExpr (Typed l t) $ map (fmap (Typed l)) xs

tcVarName :: (ProverK loc m) => Bool -> VarName Identifier loc -> TcM m (VarName GIdentifier (Typed loc))
tcVarName isWrite v@(VarName l n) = do
    exprC <- getExprC
    isAnn <- getAnn
    checkVariable isWrite (exprC==PureExpr) isAnn LocalScope (bimap mkVarId id v)

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
tcIndexCond :: (ProverK loc m) => Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcIndexCond e = tcExprTy (BaseT bool) e

-- | typechecks an index expression
tcIndexExpr :: (ProverK loc m) => IsVariadic -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcIndexExpr isVariadic e = do
    t <- if isVariadic
        then mkVariadicTyArray True False (BaseT index)
        else return (BaseT index)
    tcExprTy t e
    
tcExprTy :: (ProverK loc m) => Type -> Expression Identifier loc -> TcM m (Expression GIdentifier (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr Nothing e
    tcExprTy' ty e'
    
tcExprTy' :: (ProverK loc m) => Type -> Expression GIdentifier (Typed loc) -> TcM m (Expression GIdentifier (Typed loc))
tcExprTy' ty e' = do
    let Typed l ty' = loc e'
    ppe' <- pp e'
    x2 <- tcCoerces l True Nothing (fmap typed e') ty
    return $ fmap (Typed l) x2

tcSizes :: (ProverK loc m) => loc -> Sizes Identifier loc -> TcM m (Sizes GIdentifier (Typed loc))
tcSizes l (Sizes szs) = do
    szs' <- mapM (\x -> tcVariadicArg (tcIndexExpr (snd x)) x) $ Foldable.toList szs
    -- check array's dimension
    --tcCstrM l $ MatchTypeDimension ty $ map (mapFst (fmap typed)) szs'
    return $ Sizes $ fromListNe szs'

repeatExpr :: ProverK loc m => loc -> Bool -> Expr -> Maybe Expr -> ComplexType -> TcM m Expr
repeatExpr l isTop e Nothing t = addErrorM l (TypecheckerError (locpos l) . GenTcError (text "repeat expression without size") . Just) $ do
    let repeat = mkVarId "repeat"
    (dec,es') <- pDecCstrM l Nothing isTop False False (PIden repeat) Nothing [(False,Left e,False)] (ComplexT t)
    return $ ProcCallExpr (ComplexT t) (fmap (const $ DecT dec) $ ProcedureName () $ PIden repeat) Nothing $ mapUnLeftSndThr3 es'
repeatExpr l isTop e (Just sz) t = addErrorM l (TypecheckerError (locpos l) . GenTcError (text "repeat expression with size") . Just) $ do
    let repeat = mkVarId "repeat"
    (dec,es') <- pDecCstrM l Nothing isTop False False (PIden repeat) Nothing [(False,Left e,False),(False,Left sz,False)] (ComplexT t)
    return $ ProcCallExpr (ComplexT t) (fmap (const $ DecT dec) $ ProcedureName () $ PIden repeat) Nothing $ mapUnLeftSndThr3 es'

classifyExpr :: ProverK loc m => loc -> Bool -> Expr -> ComplexType -> TcM m Expr
classifyExpr l isTop e t = do
    let classify = mkVarId "classify"
    (dec,es') <- pDecCstrM l Nothing isTop False False (PIden classify) Nothing [(False,Left e,False)] (ComplexT t)
    return $ ProcCallExpr (ComplexT t) (fmap (const $ DecT dec) $ ProcedureName () $ PIden classify) Nothing $ mapUnLeftSndThr3 es'

shapeExpr :: ProverK loc m => loc -> Bool -> Expr -> TcM m Expr
shapeExpr l isTop e = addErrorM l (TypecheckerError (locpos l) . GenTcError (text "shape expression") . Just) $ do
    let shape = mkVarId "shape"
    let indexes = ComplexT $ CType Public index (indexExpr 1)
    (dec,es') <- pDecCstrM l Nothing isTop False False (PIden shape) Nothing [(False,Left e,False)] indexes
    return $ ProcCallExpr indexes (fmap (const $ DecT dec) $ ProcedureName () $ PIden shape) Nothing $ mapUnLeftSndThr3 es'

reshapeExpr :: ProverK loc m => loc -> Bool -> Expr -> [(Expr,IsVariadic)] -> Type -> TcM m Expr
reshapeExpr l isTop e ns ret = addErrorM l (TypecheckerError (locpos l) . GenTcError (text "reshape expression") . Just) $ do
    let reshape = mkVarId "reshape"
    (dec,ns') <- pDecCstrM l Nothing isTop False False (PIden reshape) Nothing ((False,Left e,False):map (\(x,y) -> (False,Left x,y)) ns) ret
    return $ ProcCallExpr ret (fmap (const $ DecT dec) $ ProcedureName () $ PIden reshape) Nothing $ mapUnLeftSndThr3 ns'

productIndexExpr :: (ProverK loc m) => loc -> Bool -> (Expr,IsVariadic) -> TcM m Expr
productIndexExpr l isTop (e,isVariadic) = addErrorM l (TypecheckerError (locpos l) . GenTcError (text "product index expression") . Just) $ do
    let product = mkVarId "product"
    (dec,es') <- pDecCstrM l Nothing isTop False True (PIden product) Nothing [(False,Left e,isVariadic)] (BaseT index)
    return $ ProcCallExpr (BaseT index) (fmap (const $ DecT dec) $ ProcedureName () $ PIden product) Nothing $ mapUnLeftSndThr3 es'

mapUnLeftSndThr3 = map ((\(x,Left y,z) -> (y,z)))

sumIndexExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
sumIndexExprs l isTop e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
sumIndexExprs l isTop (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 + i2)
sumIndexExprs l isTop e1 e2 = do
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing isTop False True (OIden $ OpAdd $ NoType "sumIndexExprs") Nothing [(False,Left e1,False),(False,Left e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpAdd $ DecT dec) x2)

subtractIndexExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
subtractIndexExprs l isTop e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
subtractIndexExprs l isTop (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 - i2)
subtractIndexExprs l isTop e1 e2 = do
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing isTop False True (OIden $ OpSub $ NoType "subtractIndexExprs") Nothing [(False,Left e1,False),(False,Left e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpSub $ DecT dec) x2)

multiplyIndexExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
multiplyIndexExprs l isTop e1 e2@(LitPExpr _ (IntLit _ 1)) = return e1
multiplyIndexExprs l isTop (LitPExpr l1 (IntLit l2 i1)) (LitPExpr _ (IntLit _ i2)) = return $ LitPExpr (BaseT index) $ IntLit l2 (i1 * i2)
multiplyIndexExprs l isTop e1 e2 = do
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing isTop False True (OIden $ OpMul $ NoType "multiplyIndexExprs") Nothing [(False,Left e1,False),(False,Left e2,False)] (BaseT index)
    return (BinaryExpr (BaseT index) x1 (OpMul $ DecT dec) x2)

multiplyIndexVariadicExprs :: (ProverK loc m) => loc -> Bool -> [(Expr,IsVariadic)] -> TcM m Expr
multiplyIndexVariadicExprs l isTop es = addErrorM l (TypecheckerError (locpos l) . GenTcError (text "multiply index variadic expressions") . Just) $ multiplyIndexVariadicExprs' l es
  where
    multiplyIndexVariadicExprs' :: (ProverK loc m) => loc -> [(Expr,IsVariadic)] -> TcM m Expr
    multiplyIndexVariadicExprs' l [] = return $ indexExpr 1
    multiplyIndexVariadicExprs' l [e] = multiplyIndexVariadicExpr l e
    multiplyIndexVariadicExprs' l (e:es) = do
        e' <- multiplyIndexVariadicExpr l e
        es' <- multiplyIndexVariadicExprs' l es
        multiplyIndexExprs l isTop e' es'
    multiplyIndexVariadicExpr :: (ProverK loc m) => loc -> (Expr,IsVariadic) -> TcM m Expr
    multiplyIndexVariadicExpr l (e,False) = return e
    multiplyIndexVariadicExpr l (e,True) = do
        let product = mkVarId "product"
        (dec,xs) <- pDecCstrM l Nothing isTop False True (PIden product) Nothing [(False,Left e,True)] (BaseT index)
        return $ ProcCallExpr (BaseT index) (ProcedureName (DecT dec) $ PIden product) Nothing (mapUnLeftSndThr3 xs)

landExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
landExprs l isTop e1 e2 = do
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing isTop False True (OIden $ OpSub $ NoType "landExprs") Nothing [(False,Left e1,False),(False,Left e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpLand $ DecT dec) x2)

allExprs :: ProverK loc m => loc -> Bool -> [Expr] -> TcM m Expr
allExprs l isTop [] = return $ trueExpr
allExprs l isTop es = foldr1M (landExprs l isTop) es

eqExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
eqExprs l isTop e1 e2 = do
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing isTop False True (OIden $ OpEq $ NoType "eqExprs") Nothing [(False,Left e1,False),(False,Left e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpEq $ DecT dec) x2)
    
geExprs :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m Expr
geExprs l isTop e1 e2 = do
    (dec,[(_,Left x1,_),(_,Left x2,_)]) <- pDecCstrM l Nothing isTop False True (OIden $ OpGe $ NoType "geExprs") Nothing [(False,Left e1,False),(False,Left e2,False)] (BaseT bool)
    return (BinaryExpr (BaseT bool) x1 (OpGe $ DecT dec) x2)
    
negBoolExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc)
negBoolExprLoc e = BuiltinExpr (Typed noloc $ BaseT bool) "core.eq" [(e,False),(fmap (Typed noloc) $ falseExpr,False)]

impliesExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)
impliesExprLoc e1 e2 = BuiltinExpr (Typed noloc $ BaseT bool) "core.implies" [(e1,False),(e2,False)]

andExprLoc :: Location loc => Expression iden (Typed loc) -> Expression iden (Typed loc) -> Expression iden (Typed loc)
andExprLoc e1 e2 = BuiltinExpr (Typed noloc $ BaseT bool) "core.band" [(e1,False),(e2,False)]

andExprsLoc :: Location loc => [Expression iden (Typed loc)] -> Expression iden (Typed loc)
andExprsLoc [] = fmap (Typed noloc) trueExpr
andExprsLoc [e] = e
andExprsLoc (e:es) = andExprLoc e (andExprsLoc es)






