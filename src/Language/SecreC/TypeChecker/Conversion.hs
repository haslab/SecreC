{-# LANGUAGE ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Conversion where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Utils
import Language.SecreC.Pretty

import Text.PrettyPrint

import Control.Monad.Except

type ConversionK loc m = (Location loc,MonadError SecrecError m)

type2TypeSpecifierNonVoid :: ConversionK loc m => loc -> Type -> m ((TypeSpecifier VarIdentifier (Typed loc)))
type2TypeSpecifierNonVoid l t = do
    (mb) <- type2TypeSpecifier l t
    case mb of
        Just x -> return (x)
        Nothing -> genError (locpos l) $ text "type2SizedTypeSpecifier: void type"

type2TypeSpecifier :: ConversionK loc m => loc -> Type -> m (Maybe (TypeSpecifier VarIdentifier (Typed loc)))
type2TypeSpecifier l (ComplexT t) = do
    complexType2TypeSpecifier l t
type2TypeSpecifier l b@(BaseT t) = do
    b' <- baseType2DatatypeSpecifier l t
    return (Just (TypeSpecifier (Typed l b) Nothing b' Nothing))

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



