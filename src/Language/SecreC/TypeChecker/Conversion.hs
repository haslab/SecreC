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

type2TypeSpecifierNonVoid :: ConversionK loc m => Type -> m ((TypeSpecifier VarIdentifier (Typed loc)),Maybe (Sizes VarIdentifier (Typed loc)))
type2TypeSpecifierNonVoid t = do
    (mb,sz) <- type2TypeSpecifier t
    case mb of
        Just x -> return (x,sz)
        Nothing -> genError noloc $ text "type2SizedTypeSpecifier: void type"

type2TypeSpecifier :: ConversionK loc m => Type -> m (Maybe (TypeSpecifier VarIdentifier (Typed loc)),Maybe (Sizes VarIdentifier (Typed loc)))
type2TypeSpecifier (ComplexT t) = do
    complexType2TypeSpecifier t
type2TypeSpecifier b@(BaseT t) = do
    b' <- baseType2DatatypeSpecifier t
    return (Just (TypeSpecifier (Typed noloc b) Nothing b' Nothing),Nothing)

complexType2TypeSpecifier :: ConversionK loc m => ComplexType -> m (Maybe (TypeSpecifier VarIdentifier (Typed loc)),Maybe (Sizes VarIdentifier (Typed loc)))
complexType2TypeSpecifier ct@(CType s t d sz) = do
    s' <- secType2SecTypeSpecifier s
    t' <- baseType2DatatypeSpecifier t
    sz' <- mapM sizes2Sizes sz
    return (Just (TypeSpecifier (Typed noloc $ ComplexT ct) (Just s') t' (Just $ DimSpecifier (Typed noloc $ BaseT index) $ fmap (Typed noloc) d)),sz')
complexType2TypeSpecifier Void = return (Nothing,Nothing)
complexType2TypeSpecifier c@(CVar v) = genError noloc $ text "complexType2TypeSpecifier" <+> pp c

sizes2Sizes :: ConversionK loc m => [(SExpr VarIdentifier Type,IsVariadic)] -> m (Sizes VarIdentifier (Typed loc))
sizes2Sizes = undefined

secType2SecTypeSpecifier :: ConversionK loc m => SecType -> m (SecTypeSpecifier VarIdentifier (Typed loc))
secType2SecTypeSpecifier s@Public = do
    return $ PublicSpecifier (Typed noloc $ SecT s)
secType2SecTypeSpecifier s@(Private d _) = do
    let l = Typed noloc $ SecT s
    return $ PrivateSpecifier l $ fmap (const l) d
secType2SecTypeSpecifier s@(SVar v _) = do
    let l = Typed noloc $ SecT s
    return $ PrivateSpecifier l $ fmap (const l) (DomainName l v)

baseType2DatatypeSpecifier :: ConversionK loc m => BaseType -> m (DatatypeSpecifier VarIdentifier (Typed loc))
baseType2DatatypeSpecifier b@(TyPrim p) = do
    let t = Typed noloc $ BaseT b
    return $ PrimitiveSpecifier t (fmap (const t) p)
baseType2DatatypeSpecifier b@(TApp n ts d) = do
    ts' <- fmapFstM type2TemplateTypeArgument ts
    return $ TemplateSpecifier (Typed noloc $ BaseT b) (fmap (const $ Typed noloc $ DecT d) n) ts'
baseType2DatatypeSpecifier b@(BVar v) = do
    let l = Typed noloc $ BaseT b
    return $ VariableSpecifier l (TypeName l v)

type2TemplateTypeArgument :: ConversionK loc m => Type -> m (TemplateTypeArgument VarIdentifier (Typed loc))
type2TemplateTypeArgument s@(SecT Public) = return $ PublicTemplateTypeArgument (Typed noloc s)
type2TemplateTypeArgument s@(SecT (Private (DomainName _ d) k)) = do
    let l = Typed noloc s
    return $ GenericTemplateTypeArgument l (TemplateArgName l d)
type2TemplateTypeArgument s@(SecT (SVar v k)) = do
    let l = Typed noloc s
    return $ GenericTemplateTypeArgument l (TemplateArgName l v)
type2TemplateTypeArgument (IdxT e) = do
    let l = Typed noloc (loc e)
    return $ ExprTemplateTypeArgument l (fmap (Typed noloc) e)
type2TemplateTypeArgument t@(BaseT (TyPrim p)) = do
    let l = Typed noloc t
    return $ PrimitiveTemplateTypeArgument l $ fmap (const l) p
type2TemplateTypeArgument t@(BaseT (TApp n ts d)) = do
    ts' <- fmapFstM type2TemplateTypeArgument ts
    return $ TemplateTemplateTypeArgument (Typed noloc t) (fmap (const $ Typed noloc $ DecT d) n) ts'
type2TemplateTypeArgument t = genError noloc $ text "type2TemplateTypeArgument"



