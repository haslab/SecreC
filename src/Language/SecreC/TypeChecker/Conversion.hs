{-# LANGUAGE ViewPatterns, ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Conversion where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Utils
import Language.SecreC.Pretty
import Language.SecreC.Position
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type

import Text.PrettyPrint

import Control.Monad.Except

import Data.List as List

type ConversionK loc m = (PP loc,Location loc,MonadError SecrecError m)

ftloc :: (Location loc,Functor f) => loc -> f (Typed Position) -> f (Typed loc)
ftloc l x = fmap (fmap (updpos l)) x

dec2ProcDecl :: ConversionK loc m => loc -> DecType -> m (ProcedureDeclaration VarIdentifier (Typed loc))
dec2ProcDecl l dec@(DecType _ _ _ _ _ _ _ _ (ProcType p (Left pn) pargs ret anns (Just body) _)) = do
    ret' <- type2ReturnTypeSpecifier l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    let pn' = (ProcedureName (Typed l $ DecT dec) pn)
    return $ ProcedureDeclaration (notTyped "decl" l) ret' pn' pargs' (map (ftloc l) anns) (map (ftloc l) body)
dec2ProcDecl l dec@(DecType _ _ _ _ _ _ _ _ (ProcType p (Right on) pargs ret anns (Just body) _)) = do
    ret' <- type2ReturnTypeSpecifier l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    let on' = updLoc (fmap (Typed l) on) (Typed l $ DecT dec)
    return $ OperatorDeclaration (notTyped "decl" l) ret' on' pargs' (map (ftloc l) anns) (map (ftloc l) body)
dec2ProcDecl l t = genError (locpos l) $ text "dec2ProcDecl:" <+> pp t
   
dec2FunDecl :: ConversionK loc m => loc -> DecType -> m (FunctionDeclaration VarIdentifier (Typed loc)) 
dec2FunDecl l dec@(DecType _ _ _ _ _ _ _ _ (FunType isLeak p (Left pn) pargs ret anns (Just body) _)) = do
    ret' <- type2TypeSpecifierNonVoid l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    let pn' = (ProcedureName (Typed l $ DecT dec) pn)
    return $ FunDeclaration (notTyped "decl" l) isLeak ret' pn' pargs' (map (ftloc l) anns) (ftloc l body)
dec2FunDecl l dec@(DecType _ _ _ _ _ _ _ _ (FunType isLeak p (Right on) pargs ret anns (Just body) _)) = do
    ret' <- type2TypeSpecifierNonVoid l ret
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    let on' = updLoc (fmap (Typed l) on) (Typed l $ DecT dec)
    return $ OperatorFunDeclaration (notTyped "decl" l) isLeak ret' on' pargs' (map (ftloc l) anns) (ftloc l body)
dec2FunDecl l t = genError (locpos l) $ text "dec2FunDecl:" <+> pp t

dec2AxiomDecl :: ConversionK loc m => loc -> DecType -> m (AxiomDeclaration VarIdentifier (Typed loc)) 
dec2AxiomDecl l dec@(DecType _ _ targs _ _ _ _ _ (AxiomType isLeak p pargs anns _)) = do
    let vars = map (varNameId . unConstrained . fst) targs
    targs' <- mapM (targ2TemplateQuantifier l vars) targs
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    return $ AxiomDeclaration (Typed l $ DecT dec) isLeak targs' pargs' (map (ftloc l) anns)
dec2AxiomDecl l t = genError (locpos l) $ text "dec2AxiomDecl:" <+> pp t

dec2LemmaDecl :: ConversionK loc m => loc -> DecType -> m (LemmaDeclaration VarIdentifier (Typed loc)) 
dec2LemmaDecl l dec@(DecType _ _ targs _ _ _ _ _ (LemmaType isLeak p pn pargs anns body _)) = do
    let vars = map (varNameId . unConstrained . fst) targs
    targs' <- mapM (targ2TemplateQuantifier l vars) targs
    pargs' <- mapM (parg2ProcedureParameter l) pargs
    let pn' = (ProcedureName (Typed l $ DecT dec) pn)
    return $ LemmaDeclaration (Typed l $ DecT dec) isLeak pn' targs' pargs' (map (ftloc l) anns) (fmap (map (ftloc l)) body)
dec2LemmaDecl l t = genError (locpos l) $ text "dec2LemmaDecl:" <+> pp t

dec2StructDecl :: ConversionK loc m => loc -> DecType -> m (StructureDeclaration VarIdentifier (Typed loc)) 
dec2StructDecl l dec@(DecType _ _ _ _ _ _ _ _ (StructType p sid (Just atts) _)) = do
    let atts' = map (fmap (Typed l)) atts
    let sid' = fmap (const $ Typed l $ DecT dec) sid
    return $ StructureDeclaration (notTyped "decl" l) sid' atts'
dec2StructDecl l t = genError (locpos l) $ text "dec2StructDecl:" <+> pp t

targ2TemplateQuantifier :: ConversionK loc m => loc -> [VarIdentifier] -> (Constrained Var,IsVariadic) -> m (TemplateQuantifier VarIdentifier (Typed loc))
targ2TemplateQuantifier l vars cv@(Constrained v@(VarName vt vn) e,isVariadic) = case (typeClass "targ" vt,vt) of
    (isDomain -> True,KindT k) -> do
        mbk <- case k of
            PublicK -> return Nothing
            PrivateK kn -> return $ Just $ fmap (const $ Typed l $ KindT k) $ kn
            KVar kv False -> return $ Just $ KindName (Typed l $ KindT k) kv
            KVar kv True -> if List.elem kv vars
                then return $ Just $ KindName (Typed l $ KindT k) kv
                else genError (locpos l) $ text "targ2TemplateQuantifier: unsupported kind type" <+> pp k
        return $ DomainQuantifier (notTyped "targ" l) isVariadic (DomainName (Typed l vt) vn) mbk
    (isKind -> True,KType isPriv) -> do
        return $ KindQuantifier (notTyped "targ" l) isPriv isVariadic (KindName (Typed l vt) vn)
    (isType -> True,vt) -> do
        return $ DataQuantifier (notTyped "targ" l) isVariadic $ TypeName (Typed l vt) vn
    (isVariable -> True,vt) -> do
        return $ DimensionQuantifier (notTyped "targ" l) isVariadic (VarName (Typed l vt) vn) $ fmap (fmap (Typed l)) e
    otherwise -> genError (locpos l) $ text "targ2TemplateQuantifier:" <+> pp cv

parg2ProcedureParameter :: ConversionK loc m => loc -> (Bool,Var,IsVariadic) -> m (ProcedureParameter VarIdentifier (Typed loc))
parg2ProcedureParameter l (isConst,v,isVariadic) = do
    let t = if isVariadic then variadicBase (loc v) else loc v
    t' <- type2TypeSpecifierNonVoid l t
    return $ ProcedureParameter (Typed l $ loc v) isConst t' isVariadic (fmap (Typed l) v)

type2TypeSpecifierNonVoid :: ConversionK loc m => loc -> Type -> m ((TypeSpecifier VarIdentifier (Typed loc)))
type2TypeSpecifierNonVoid l t = do
    (mb) <- type2TypeSpecifier l t
    case mb of
        Just x -> return (x)
        Nothing -> genError (locpos l) $ text "type2SizedTypeSpecifier: void type"

type2ReturnTypeSpecifier :: ConversionK loc m => loc -> Type -> m (ReturnTypeSpecifier VarIdentifier (Typed loc))
type2ReturnTypeSpecifier l t = do
    mb <- type2TypeSpecifier l t
    let mbt = maybe (ComplexT Void) (typed . loc) mb
    return $ ReturnType (Typed l mbt) mb

type2TypeSpecifier :: ConversionK loc m => loc -> Type -> m (Maybe (TypeSpecifier VarIdentifier (Typed loc)))
type2TypeSpecifier l (ComplexT t) = do
    complexType2TypeSpecifier l t
type2TypeSpecifier l b@(BaseT t) = do
    b' <- baseType2DatatypeSpecifier l t
    return (Just (TypeSpecifier (Typed l b) Nothing b' Nothing))
type2TypeSpecifier l t = error $ "type2TypeSpecifier: " ++ ppr l ++ " " ++ ppr t

complexType2TypeSpecifier :: ConversionK loc m => loc -> ComplexType -> m (Maybe (TypeSpecifier VarIdentifier (Typed loc)))
complexType2TypeSpecifier l ct@(CType s t d) = do
    s' <- secType2SecTypeSpecifier l s
    t' <- baseType2DatatypeSpecifier l t
    return (Just (TypeSpecifier (Typed l $ ComplexT ct) (Just s') t' (Just $ DimSpecifier (Typed l $ BaseT index) $ fmap (Typed l) d)))
complexType2TypeSpecifier l Void = return (Nothing)
complexType2TypeSpecifier l c@(CVar v) = genError (locpos l) $ text "complexType2TypeSpecifier" <+> pp c

sizes2Sizes :: ConversionK loc m => [(Expr,IsVariadic)] -> m (Sizes VarIdentifier (Typed loc))
sizes2Sizes = undefined

secType2SecTypeSpecifier :: ConversionK loc m => loc -> SecType -> m (SecTypeSpecifier VarIdentifier (Typed loc))
secType2SecTypeSpecifier l s@Public = do
    return $ PublicSpecifier (Typed l $ SecT s)
secType2SecTypeSpecifier l s@(Private d _) = do
    let tl = Typed l $ SecT s
    return $ PrivateSpecifier tl $ fmap (const tl) d
secType2SecTypeSpecifier l s@(SVar v _) = do
    let tl = Typed l $ SecT s
    return $ PrivateSpecifier tl $ fmap (const tl) (DomainName tl v)

baseType2DatatypeSpecifier :: ConversionK loc m => loc -> BaseType -> m (DatatypeSpecifier VarIdentifier (Typed loc))
baseType2DatatypeSpecifier l b@(TyPrim p) = do
    let t = Typed l $ BaseT b
    return $ PrimitiveSpecifier t (fmap (const t) p)
baseType2DatatypeSpecifier l b@(TApp n ts d) = do
    ts' <- fmapFstM (type2TemplateTypeArgument l) ts
    return $ TemplateSpecifier (Typed l $ BaseT b) (fmap (const $ Typed l $ DecT d) n) ts'
baseType2DatatypeSpecifier l b@(BVar v) = do
    let tl = Typed l $ BaseT b
    return $ VariableSpecifier tl (TypeName tl v)
baseType2DatatypeSpecifier l t@(MSet b) = do
    b' <- baseType2DatatypeSpecifier l b
    return $ MultisetSpecifier (Typed l $ BaseT t) b'
--baseType2DatatypeSpecifier l t = genError (locpos l) $ text "baseType2DatatypeSpecifier:" <+> pp t

type2TemplateTypeArgument :: ConversionK loc m => loc -> Type -> m (TemplateTypeArgument VarIdentifier (Typed loc))
type2TemplateTypeArgument l s@(SecT Public) = return $ PublicTemplateTypeArgument (Typed l s)
type2TemplateTypeArgument l s@(SecT (Private (DomainName _ d) k)) = do
    let tl = Typed l s
    return $ GenericTemplateTypeArgument tl (TemplateArgName tl d)
type2TemplateTypeArgument l s@(SecT (SVar v k)) = do
    let tl = Typed l s
    return $ GenericTemplateTypeArgument tl (TemplateArgName tl v)
type2TemplateTypeArgument l (IdxT e) = do
    let tl = Typed l (loc e)
    return $ ExprTemplateTypeArgument tl (fmap (Typed l) e)
type2TemplateTypeArgument l t@(BaseT (TyPrim p)) = do
    let tl = Typed noloc t
    return $ PrimitiveTemplateTypeArgument tl $ fmap (const tl) p
type2TemplateTypeArgument l t@(BaseT (TApp n ts d)) = do
    ts' <- fmapFstM (type2TemplateTypeArgument l) ts
    return $ TemplateTemplateTypeArgument (Typed l t) (fmap (const $ Typed l $ DecT d) n) ts'
type2TemplateTypeArgument l t@(BaseT (BVar v)) = do
    let tl = Typed l t
    return $ GenericTemplateTypeArgument tl $ (TemplateArgName tl v)
type2TemplateTypeArgument l t = genError (locpos l) $ text "type2TemplateTypeArgument" <+> pp t



