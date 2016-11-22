{-# LANGUAGE ViewPatterns, ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Conversion where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.Prover.Base
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Utils
import Language.SecreC.Pretty
import Language.SecreC.Position
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type

import Data.Graph.Inductive.Graph as Graph

import Text.PrettyPrint

import Control.Monad.Except

import Data.List as List

type ConversionK loc m = ProverK loc m

ftloc :: (Location loc,Functor f) => loc -> f (Typed Position) -> f (Typed loc)
ftloc l x = fmap (fmap (updpos l)) x

dec2ProcDecl :: ConversionK loc m => loc -> DecType -> TcM m (ProcedureDeclaration GIdentifier (Typed loc))
dec2ProcDecl l dec@(DecType _ _ _ hctx bctx _ (ProcType p pn@(PIden _) pargs ret anns (Just body) _)) = do
    ret' <- type2ReturnTypeSpecifier l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    bctx' <- decCtx2TemplateContext l =<< mergeHeadDecCtx l hctx bctx
    let pn' = (ProcedureName (Typed l $ DecT dec) $ funit pn)
    return (ProcedureDeclaration (notTyped "decl" l) ret' pn' pargs' bctx' (map (ftloc l) anns) (map (ftloc l) body))
dec2ProcDecl l dec@(DecType _ _ _ hctx bctx _ (ProcType p (OIden on) pargs ret anns (Just body) _)) = do
    ret' <- type2ReturnTypeSpecifier l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    bctx' <- decCtx2TemplateContext l =<< mergeHeadDecCtx l hctx bctx
    let on' = updLoc (fmap (Typed l) on) (Typed l $ DecT dec)
    return (OperatorDeclaration (notTyped "decl" l) ret' on' pargs' bctx' (map (ftloc l) anns) (map (ftloc l) body))
dec2ProcDecl l t = do
    ppt <- pp t
    genError (locpos l) $ text "dec2ProcDecl:" <+> ppt
   
dec2FunDecl :: ConversionK loc m => loc -> DecType -> TcM m (FunctionDeclaration GIdentifier (Typed loc)) 
dec2FunDecl l dec@(DecType _ _ _ hctx bctx _ (FunType isLeak p pn@(PIden _) pargs ret anns (Just body) _)) = do
    ret' <- type2TypeSpecifierNonVoid l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    bctx' <- decCtx2TemplateContext l =<< mergeHeadDecCtx l hctx bctx
    let pn' = (ProcedureName (Typed l $ DecT dec) $ funit pn)
    return (FunDeclaration (notTyped "decl" l) isLeak ret' pn' pargs' bctx' (map (ftloc l) anns) (ftloc l body))
dec2FunDecl l dec@(DecType _ _ _ hctx bctx _ (FunType isLeak p (OIden on) pargs ret anns (Just body) _)) = do
    ret' <- type2TypeSpecifierNonVoid l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    bctx' <- decCtx2TemplateContext l =<< mergeHeadDecCtx l hctx bctx
    let on' = updLoc (fmap (Typed l) on) (Typed l $ DecT dec)
    return (OperatorFunDeclaration (notTyped "decl" l) isLeak ret' on' pargs' bctx' (map (ftloc l) anns) (ftloc l body))
dec2FunDecl l t = do
    ppt <- pp t
    genError (locpos l) $ text "dec2FunDecl:" <+> ppt

dec2AxiomDecl :: ConversionK loc m => loc -> DecType -> TcM m (AxiomDeclaration GIdentifier (Typed loc)) 
dec2AxiomDecl l dec@(DecType _ _ targs _ _ _ (AxiomType isLeak p pargs anns _)) = do
    let vars = map (varNameId . unConstrained . fst) targs
    targs' <- mapM (targ2TemplateQuantifier l vars) targs
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    return $ AxiomDeclaration (Typed l $ DecT dec) isLeak targs' pargs' (map (ftloc l) anns)
dec2AxiomDecl l t = do
    ppt <- pp t
    genError (locpos l) $ text "dec2AxiomDecl:" <+> ppt

decCtx2TemplateContext :: ConversionK loc m => loc -> DecCtx -> TcM m (TemplateContext GIdentifier (Typed loc))
decCtx2TemplateContext l dec@(DecCtx Nothing _ _) = return $ TemplateContext (Typed l (DecCtxT dec)) Nothing
decCtx2TemplateContext l dec@(DecCtx (Just _) d _) = liftM (TemplateContext (Typed l (DecCtxT dec)) . Just) $ cstrs2Context l (pureCstrs d)
    where
    cstrs2Context :: ConversionK loc m => loc -> TCstrGraph -> TcM m [ContextConstraint GIdentifier (Typed loc)]
    cstrs2Context l g = mapM (cstr2Context l . unLoc . snd) $ Graph.labNodes g
    cstr2Context :: ConversionK loc m => loc -> TCstr -> TcM m (ContextConstraint GIdentifier (Typed loc))
    cstr2Context l (TcK k st) = tcCstr2Context l k st
    cstr2Context l (CheckK k _) = do
        ppk <- pp k
        genError (locpos l) $ text "cstr2Context: check" <+> ppk
    cstr2Context l (HypK k _) = do
        ppk <- pp k
        genError (locpos l) $ text "cstr2Context: hypothesis" <+> ppk
    tcCstr2Context :: ConversionK loc m => loc -> TcCstr -> CstrState -> TcM m (ContextConstraint GIdentifier (Typed loc))
    tcCstr2Context l k@(TDec dk es (TIden n) ts x) st = do
        let tn' = TypeName (Typed l $ DecT x) $ TIden n
        ts' <- mapM (mapFstM (type2TemplateTypeArgument l)) ts
        return $ ContextTDec (Typed l $ TCstrT $ TcK k st) (cstrExprC st) tn' ts'
    tcCstr2Context l k@(PDec dk es (PIden n) ts args ret x) st = do
        ret' <- type2ReturnTypeSpecifier l ret
        let pn' = ProcedureName (Typed l $ DecT x) $ PIden n
        ts' <- mapM (mapM (mapFstM (type2TemplateTypeArgument l))) ts
        args' <- mapM (decPArg2CtxPArg l) args
        let Just kind = decKind2CstrKind $ cstrDecK st
        return $ ContextPDec (Typed l $ TCstrT $ TcK k st) (cstrExprC st) (cstrIsLeak st) (cstrIsAnn st) kind ret' pn' ts' args'
    tcCstr2Context l k@(PDec dk es (OIden o) ts args ret _) st = do
        ret' <- type2ReturnTypeSpecifier l ret
        let o' = fmap (Typed l) o
        ts' <- mapM (mapM (mapFstM (type2TemplateTypeArgument l))) ts
        args' <- mapM (decPArg2CtxPArg l) args
        let Just kind = decKind2CstrKind $ cstrDecK st
        return $ ContextODec (Typed l $ TCstrT $ TcK k st) (cstrExprC st) (cstrIsLeak st) (cstrIsAnn st) kind ret' o' ts' args'
    tcCstr2Context l k st = do
        ppk <- pp k
        genError (locpos l) $ text "tcCstr2Context:" <+> ppk

decKind2CstrKind :: DecKind -> Maybe CstrKind
decKind2CstrKind PKind = Just CstrProcedure
decKind2CstrKind FKind = Just CstrFunction
decKind2CstrKind LKind = Just CstrLemma
decKind2CstrKind k = Nothing

cstrKind2DecKind :: CstrKind -> DecKind
cstrKind2DecKind CstrProcedure = PKind
cstrKind2DecKind CstrFunction = FKind
cstrKind2DecKind CstrLemma = LKind

decPArg2CtxPArg :: ConversionK loc m => loc -> (IsConst,Either Expr Type,IsVariadic) -> TcM m (CtxPArg GIdentifier (Typed loc))
decPArg2CtxPArg l (isConst,Left e,isVariadic) = return $ CtxExprPArg (Typed l $ IdxT e) isConst (fmap (Typed l) e) isVariadic
decPArg2CtxPArg l (isConst,Right t,isVariadic) = do
    t' <- type2TypeSpecifierNonVoid l t
    return $ CtxTypePArg (Typed l t) isConst t' isVariadic

dec2LemmaDecl :: ConversionK loc m => loc -> DecType -> TcM m (LemmaDeclaration GIdentifier (Typed loc)) 
dec2LemmaDecl l dec@(DecType _ _ targs hctx bctx _ (LemmaType isLeak p pn pargs anns body _)) = do
    let vars = map (varNameId . unConstrained . fst) targs
    targs' <- mapM (targ2TemplateQuantifier l vars) targs
    hctx' <- decCtx2TemplateContext l hctx
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    bctx' <- decCtx2TemplateContext l bctx
    let pn' = (ProcedureName (Typed l $ DecT dec) $ funit pn)
    return $ LemmaDeclaration (Typed l $ DecT dec) isLeak pn' targs' hctx' pargs' bctx' (map (ftloc l) anns) (fmap (map (ftloc l)) body)
dec2LemmaDecl l t = do
    ppt <- pp t
    genError (locpos l) $ text "dec2LemmaDecl:" <+> ppt

dec2StructDecl :: ConversionK loc m => loc -> DecType -> TcM m (StructureDeclaration GIdentifier (Typed loc)) 
dec2StructDecl l dec@(DecType _ _ _ hctx bctx _ (StructType p sid (Just atts) _)) = do
    bctx' <- decCtx2TemplateContext l =<< mergeHeadDecCtx l hctx bctx
    let atts' = map (fmap (Typed l)) atts
    let sid' = fmap (const $ Typed l $ DecT dec) $ TypeName () sid
    return (StructureDeclaration (notTyped "decl" l) sid' bctx' atts')
dec2StructDecl l t = do
    ppt <- pp t
    genError (locpos l) $ text "dec2StructDecl:" <+> ppt

targ2TemplateQuantifier :: ConversionK loc m => loc -> [GIdentifier] -> (Constrained Var,IsVariadic) -> TcM m (TemplateQuantifier GIdentifier (Typed loc))
targ2TemplateQuantifier l vars cv@(Constrained v@(VarName vt vn) e,isVariadic) = case (typeClass "targ" vt,vt) of
    (isDomain -> True,KindT k) -> do
        mbk <- case k of
            PublicK -> return Nothing
            PrivateK kn -> return $ Just $ fmap (const $ Typed l $ KindT k) $ KindName () kn
            KVar kv Nothing -> return $ Just $ KindName (Typed l $ KindT k) $ VIden kv
            KVar kv (Just NonPublicClass) -> if List.elem (VIden kv) vars
                then return $ Just $ KindName (Typed l $ KindT k) $ VIden kv
                else do
                    ppk <- pp k
                    genError (locpos l) $ text "targ2TemplateQuantifier: unsupported kind type" <+> ppk
        return $ DomainQuantifier (notTyped "targ" l) isVariadic (DomainName (Typed l vt) vn) mbk
    (isKind -> True,KType isPriv) -> do
        return $ KindQuantifier (notTyped "targ" l) isPriv isVariadic (KindName (Typed l vt) vn)
    (isType -> True,BType c) -> do
        return $ DataQuantifier (notTyped "targ" l) c isVariadic $ TypeName (Typed l vt) vn
    (isVariable -> True,vt) -> do
        return $ DimensionQuantifier (notTyped "targ" l) isVariadic (VarName (Typed l vt) vn) $ fmap (fmap (Typed l)) e
    otherwise -> do
        ppcv <- pp cv
        genError (locpos l) $ text "targ2TemplateQuantifier:" <+> ppcv

parg2ProcedureParameter :: ConversionK loc m => loc -> (Bool,Var,IsVariadic) -> TcM m (ProcedureParameter GIdentifier (Typed loc))
parg2ProcedureParameter l (isConst,v,isVariadic) = do
    let t = if isVariadic then variadicBase (loc v) else loc v
    t' <- type2TypeSpecifierNonVoid l t
    return $ ProcedureParameter (Typed l $ loc v) isConst t' isVariadic (fmap (Typed l) v)

type2TypeSpecifierNonVoid :: ConversionK loc m => loc -> Type -> TcM m ((TypeSpecifier GIdentifier (Typed loc)))
type2TypeSpecifierNonVoid l t = do
    (mb) <- type2TypeSpecifier l t
    case mb of
        Just x -> return (x)
        Nothing -> genError (locpos l) $ text "type2SizedTypeSpecifier: void type"

type2ReturnTypeSpecifier :: ConversionK loc m => loc -> Type -> TcM m (ReturnTypeSpecifier GIdentifier (Typed loc))
type2ReturnTypeSpecifier l t = do
    mb <- type2TypeSpecifier l t
    let mbt = maybe (ComplexT Void) (typed . loc) mb
    return $ ReturnType (Typed l mbt) mb

type2TypeSpecifier :: ConversionK loc m => loc -> Type -> TcM m (Maybe (TypeSpecifier GIdentifier (Typed loc)))
type2TypeSpecifier l (ComplexT t) = do
    complexType2TypeSpecifier l t
type2TypeSpecifier l b@(BaseT t) = do
    b' <- baseType2DatatypeSpecifier l t
    return (Just (TypeSpecifier (Typed l b) Nothing b' Nothing))
type2TypeSpecifier l t = do
    ppl <- ppr l
    ppt <- ppr t
    error $ "type2TypeSpecifier: " ++ ppl ++ " " ++ ppt

complexType2TypeSpecifier :: ConversionK loc m => loc -> ComplexType -> TcM m (Maybe (TypeSpecifier GIdentifier (Typed loc)))
complexType2TypeSpecifier l ct@(CType s t d) = do
    s' <- secType2SecTypeSpecifier l s
    t' <- baseType2DatatypeSpecifier l t
    return (Just (TypeSpecifier (Typed l $ ComplexT ct) (Just s') t' (Just $ DimSpecifier (Typed l $ BaseT index) $ fmap (Typed l) d)))
complexType2TypeSpecifier l Void = return (Nothing)
complexType2TypeSpecifier l c@(CVar v _) = do
    ppc <- pp c
    genError (locpos l) $ text "complexType2TypeSpecifier" <+> ppc

sizes2Sizes :: ConversionK loc m => [(Expr,IsVariadic)] -> TcM m (Sizes GIdentifier (Typed loc))
sizes2Sizes = undefined

secType2SecTypeSpecifier :: ConversionK loc m => loc -> SecType -> TcM m (SecTypeSpecifier GIdentifier (Typed loc))
secType2SecTypeSpecifier l s@Public = do
    return $ PublicSpecifier (Typed l $ SecT s)
secType2SecTypeSpecifier l s@(Private d _) = do
    let tl = Typed l $ SecT s
    return $ PrivateSpecifier tl $ fmap (const tl) $ DomainName () d
secType2SecTypeSpecifier l s@(SVar v _) = do
    let tl = Typed l $ SecT s
    return $ PrivateSpecifier tl $ fmap (const tl) (DomainName tl $ VIden v)

baseType2DatatypeSpecifier :: ConversionK loc m => loc -> BaseType -> TcM m (DatatypeSpecifier GIdentifier (Typed loc))
baseType2DatatypeSpecifier l b@(TyPrim p) = do
    let t = Typed l $ BaseT b
    return $ PrimitiveSpecifier t (fmap (const t) p)
baseType2DatatypeSpecifier l b@(TApp n ts d) = do
    ts' <- fmapFstM (type2TemplateTypeArgument l) ts
    return $ TemplateSpecifier (Typed l $ BaseT b) (fmap (const $ Typed l $ DecT d) $ TypeName () n) ts'
baseType2DatatypeSpecifier l b@(BVar v c) = do
    let tl = Typed l $ BaseT b
    return $ VariableSpecifier tl (TypeName tl (VIden v))
baseType2DatatypeSpecifier l t@(MSet b) = do
    b' <- type2TypeSpecifierNonVoid l $ ComplexT b
    return $ MultisetSpecifier (Typed l $ BaseT t) b'
baseType2DatatypeSpecifier l t@(Set b) = do
    b' <- type2TypeSpecifierNonVoid l $ ComplexT b
    return $ SetSpecifier (Typed l $ BaseT t) b'
--baseType2DatatypeSpecifier l t = genError (locpos l) $ text "baseType2DatatypeSpecifier:" <+> pp t

type2TemplateTypeArgument :: ConversionK loc m => loc -> Type -> TcM m (TemplateTypeArgument GIdentifier (Typed loc))
type2TemplateTypeArgument l s@(SecT Public) = return $ PublicTemplateTypeArgument (Typed l s)
type2TemplateTypeArgument l s@(SecT (Private d k)) = do
    let tl = Typed l s
    return $ GenericTemplateTypeArgument tl (TemplateArgName tl d)
type2TemplateTypeArgument l s@(SecT (SVar v k)) = do
    let tl = Typed l s
    return $ GenericTemplateTypeArgument tl (TemplateArgName tl $ VIden v)
type2TemplateTypeArgument l (IdxT e) = do
    let tl = Typed l (loc e)
    return $ ExprTemplateTypeArgument tl (fmap (Typed l) e)
type2TemplateTypeArgument l t@(BaseT (TyPrim p)) = do
    let tl = Typed noloc t
    return $ PrimitiveTemplateTypeArgument tl $ fmap (const tl) p
type2TemplateTypeArgument l t@(BaseT (TApp n ts d)) = do
    ts' <- fmapFstM (type2TemplateTypeArgument l) ts
    return $ TemplateTemplateTypeArgument (Typed l t) (fmap (const $ Typed l $ DecT d) $ TypeName () n) ts'
type2TemplateTypeArgument l t@(BaseT (BVar v c)) = do
    let tl = Typed l t
    return $ GenericTemplateTypeArgument tl $ (TemplateArgName tl $ VIden v)
type2TemplateTypeArgument l t = do
    ppt <- pp t
    genError (locpos l) $ text "type2TemplateTypeArgument" <+> ppt

