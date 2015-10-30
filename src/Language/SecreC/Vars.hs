{-# LANGUAGE DeriveFunctor, FlexibleContexts, DeriveDataTypeable, TypeFamilies, MultiParamTypeClasses #-}

module Language.SecreC.Vars where

import Prelude hiding (foldr)

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Utils
import Language.SecreC.Parser.Tokens

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Data.Generics

varNameId :: VarName loc -> Identifier
varNameId (VarName _ i) = i

type Substs a = (VarOf a -> Maybe (SubstOf a))

class Vars a => Subst a where
    type SubstOf a :: *
    subst :: Substs a -> a -> a
    
    emptySubsts :: Proxy a -> Substs a
    emptySubsts _ = const Nothing
    
    appendSubsts :: Proxy a -> Substs a -> Substs a -> Substs a
    appendSubsts _ f g v = case f v of
        Nothing -> g v
        Just x -> Just x

substFromList :: (Subst a,Eq (VarOf a)) => Proxy a -> [(VarOf a,SubstOf a)] -> Substs a
substFromList p [] = emptySubsts p
substFromList p ((v,s):xs) = appendSubsts p f (substFromList p xs)
    where f x = if x==v then Just s else Nothing

substTraversable :: (Traversable t,Subst a) => Substs a -> t a -> t a
substTraversable s = fmap (subst s)


class Ord (VarOf a) => Vars a where
    type VarOf a :: *
    
    -- | Free variables
    fvs :: a -> Set (VarOf a)
    -- | Bound variables
    bvs :: a -> Set (VarOf a)
    -- | Apply a variable substitution

-- | A Variable with name-based equality
data ScVar loc = ScVar loc Identifier
  deriving (Read,Show,Data,Typeable,Functor)

instance Eq (ScVar loc) where
    (ScVar _ a) == (ScVar _ b) = a == b
instance Ord (ScVar loc) where
    compare (ScVar _ a) (ScVar _ b) = compare a b

instance Vars (Module loc) where
    type VarOf (Module loc) = ScVar loc
    fvs (Module _ _ p) = fvs p
    bvs (Module _ _ p) = bvs p

fvsFoldable :: (Foldable t,Vars a) => t a -> Set (VarOf a)
fvsFoldable = foldr (\x s -> fvs x `Set.union` (s `Set.difference` bvs x)) Set.empty
bvsFoldable :: (Foldable t,Vars a) => t a -> Set (VarOf a)
bvsFoldable = foldr (\x s -> fvs x `Set.union` s) Set.empty

fvsBut x y = fvs x `Set.union` (y `Set.difference` bvs x)

fvsMaybe :: Vars a => Maybe a -> Set (VarOf a)
fvsMaybe = maybe Set.empty fvs
bvsMaybe :: Vars a => Maybe a -> Set (VarOf a)
bvsMaybe = maybe Set.empty bvs

instance Vars (Program loc) where
    type VarOf (Program loc) = ScVar loc
    fvs (Program _ _ gds) = fvsFoldable gds
    bvs (Program _ _ gds) = bvsFoldable gds
    
instance Vars (GlobalDeclaration loc) where
    type VarOf (GlobalDeclaration loc) = ScVar loc
    fvs (GlobalVariable _ x) = fvs x
    fvs (GlobalDomain _ x) = fvs x
    fvs (GlobalKind _ x) = fvs x
    fvs (GlobalProcedure _ x) = fvs x
    fvs (GlobalStructure _ x) = fvs x
    fvs (GlobalTemplate _ x) = fvs x
    bvs (GlobalVariable _ x) = bvs x
    bvs (GlobalDomain _ x) = bvs x
    bvs (GlobalKind _ x) = bvs x
    bvs (GlobalProcedure _ x) = bvs x
    bvs (GlobalStructure _ x) = bvs x
    bvs (GlobalTemplate _ x) = bvs x

instance Vars (VariableInitialization loc) where
    type VarOf (VariableInitialization loc) = ScVar loc
    fvs (VariableInitialization l v dim e) = ((maybe Set.empty fvs dim) `Set.union` (maybe Set.empty fvs e)) `Set.difference` fvs v
    bvs (VariableInitialization l v dim e) = bvs v 

instance Vars (Sizes loc) where
    type VarOf (Sizes loc) = ScVar loc
    fvs (Sizes xs) = foldr (\e u -> fvs e `Set.union` u) Set.empty xs
    bvs (Sizes xs) = foldr (\e u -> bvs e `Set.union` u) Set.empty xs

instance Vars (Expression loc) where
    type VarOf (Expression loc) = ScVar loc
    fvs (BinaryAssign _ e1 op e2) = fvs e1 `Set.union` fvs e2
    fvs (QualExpr l e ts) = fvs e `Set.union` fvsFoldable ts
    fvs (CondExpr l e1 e2 e3) = fvs e1 `Set.union` fvs e2 `Set.union` fvs e3
    fvs (BinaryExpr l e1 o e2) = fvs e1 `Set.union` fvs e2
    fvs (UminusExpr l e) = fvs e
    fvs (UnegExpr l e) = fvs e
    fvs (UinvExpr l e) = fvs e
    fvs (Upost l e) = fvs e
    fvs (PrefixInc l e) = fvs e
    fvs (PrefixDec l e) = fvs e
    fvs (PostfixInc l e) = fvs e
    fvs (PostfixDec l e) = fvs e
    fvs (PrimCastExpr l p e) = fvs p `Set.union` fvs e
    fvs (VarCastExpr l t e) = fvs t `Set.union` fvs e
    
    bvs (BinaryAssign _ e1 op e2) = bvs e1 `Set.union` bvs e2
    bvs (QualExpr l e ts) = bvs e `Set.union` bvsFoldable ts
    bvs (CondExpr l e1 e2 e3) = bvs e1 `Set.union` bvs e2 `Set.union` bvs e3    
    bvs (BinaryExpr l e1 o e2) = bvs e1 `Set.union` bvs e2
    bvs (UminusExpr l e) = bvs e
    bvs (UnegExpr l e) = bvs e
    bvs (UinvExpr l e) = bvs e
    bvs (Upost l e) = bvs e
    bvs (PrefixInc l e) = bvs e
    bvs (PrefixDec l e) = bvs e
    bvs (PostfixInc l e) = bvs e
    bvs (PostfixDec l e) = bvs e
    bvs (PrimCastExpr l p e) = bvs p `Set.union` bvs e
    bvs (VarCastExpr l t e) = bvs t `Set.union` bvs e

instance Vars (PostfixExpression loc) where
    type VarOf (PostfixExpression loc) = ScVar loc
    fvs (DeclassifyExpr l e) = fvs e
    fvs (SizeExpr l e) = fvs e
    fvs (ShapeExpr l e) = fvs e
    fvs (PostCatExpr l e) = fvs e
    fvs (DomainIdExpr l t) = fvs t
    fvs (ReshapeExpr l es) = fvsFoldable es
    fvs (ToStringExpr l e) = fvs e
    fvs (StrlenExpr l e) = fvs e
    fvs (StringFromBytesExpr l e) = fvs e
    fvs (BytesFromStringExpr l e) = fvs e
    fvs (ProcCallExpr l n e) = fvs n `Set.union` fvsFoldable e
    fvs (PostIndexExpr l e s) = fvs e `Set.union` fvsFoldable s
    fvs (SelectionExpr l e v) = fvs e `Set.union` fvs v
    fvs (PostPrimExpr l e) = fvs e
    bvs (DeclassifyExpr l e) = bvs e
    bvs (SizeExpr l e) = bvs e
    bvs (ShapeExpr l e) = bvs e
    bvs (PostCatExpr l e) = bvs e
    bvs (DomainIdExpr l t) = bvs t
    bvs (ReshapeExpr l es) = bvsFoldable es
    bvs (ToStringExpr l e) = bvs e
    bvs (StrlenExpr l e) = bvs e
    bvs (StringFromBytesExpr l e) = bvs e
    bvs (BytesFromStringExpr l e) = bvs e
    bvs (ProcCallExpr l n e) = bvs n `Set.union` bvsFoldable e
    bvs (PostIndexExpr l e s) = bvs e `Set.union` bvsFoldable s
    bvs (SelectionExpr l e v) = bvs e `Set.union` bvs v
    bvs (PostPrimExpr l e) = bvs e  

instance Vars (CatExpression loc) where
    type VarOf (CatExpression loc) = ScVar loc
    fvs (CatExpr l e1 e2 _) = fvs e1 `Set.union` fvs e2
    bvs (CatExpr l e1 e2 _) = bvs e1 `Set.union` bvs e2

instance Vars (Index loc) where
    type VarOf (Index loc) = ScVar loc
    fvs (IndexSlice l e1 e2) = fvsMaybe e1 `Set.union` fvsMaybe e2
    fvs (IndexInt l e) = fvs e
    bvs (IndexSlice l e1 e2) = bvsMaybe e1 `Set.union` bvsMaybe e2
    bvs (IndexInt l e) = bvs e

instance Vars (StructureDeclaration loc) where
    type VarOf (StructureDeclaration loc) = ScVar loc
    fvs (StructureDeclaration l t as) = fvs t `Set.union` fvsFoldable as
    bvs (StructureDeclaration l t as) = bvs t `Set.union` bvsFoldable as

instance Vars (QualifiedType loc) where
    type VarOf (QualifiedType loc) = ScVar loc
    fvs (PublicQualifiedType l) = Set.empty
    fvs (PrimitiveQualifiedType l t) = fvs t
    fvs (DimQualifiedType l t) = fvs t
    fvs (GenericQualifiedType l n) = Set.empty
    bvs (PublicQualifiedType l) = Set.empty
    bvs (PrimitiveQualifiedType l t) = bvs t
    bvs (DimQualifiedType l t) = bvs t
    bvs (GenericQualifiedType l n) = Set.empty

instance Vars (PrimaryExpression loc) where
    type VarOf (PrimaryExpression loc) = ScVar loc
    fvs (PExpr l e) = fvs e
    fvs (ArrayConstructorPExpr l es) = fvsFoldable es
    fvs (RVariablePExpr l v) = fvs v
    fvs (LitPExpr l i) = fvs i
    bvs (PExpr l e) = bvs e
    bvs (ArrayConstructorPExpr l es) = bvsFoldable es
    bvs (RVariablePExpr l v) = bvs v
    bvs (LitPExpr l i) = bvs i

instance Vars (Attribute loc) where
    type VarOf (Attribute loc) = ScVar loc
    fvs (Attribute l t a) = fvs t `Set.union` fvs a
    bvs (Attribute l t a) = bvs t `Set.union` bvs a

instance Vars (AttributeName loc) where
    type VarOf (AttributeName loc) = ScVar loc
    fvs = const Set.empty
    bvs = const Set.empty

instance Vars (Literal loc) where
    type VarOf (Literal loc) = ScVar loc
    fvs = const Set.empty
    bvs = const Set.empty

instance Vars (VariableDeclaration loc) where
    type VarOf (VariableDeclaration loc) = ScVar loc
    fvs (VariableDeclaration l t es) = fvs t `Set.union` fvsFoldable es
    bvs (VariableDeclaration l t es) = bvs t `Set.union` bvsFoldable es

instance Vars (DomainDeclaration loc) where
    type VarOf (DomainDeclaration loc) = ScVar loc
    fvs (Domain _ d k) = fvs k
    bvs (Domain _ d k) = bvs d `Set.union` bvs k

instance Vars (KindDeclaration loc) where
    type VarOf (KindDeclaration loc) = ScVar loc
    fvs (Kind _ k) = Set.empty
    bvs (Kind _ k) = fvs k

instance Vars (TemplateDeclaration loc) where
    type VarOf (TemplateDeclaration loc) = ScVar loc
    fvs (TemplateStructureDeclaration l es s) = fvsFoldable es `Set.union` fvs s
    fvs (TemplateProcedureDeclaration l es p) = fvsFoldable es `Set.union` fvs p
    bvs (TemplateStructureDeclaration l es s) = bvsFoldable es `Set.union` bvs s
    bvs (TemplateProcedureDeclaration l es p) = bvsFoldable es `Set.union` bvs p

instance Vars (TemplateQuantifier loc) where
    type VarOf (TemplateQuantifier loc) = ScVar loc
    fvs (DomainQuantifier l n k) = fvs n `Set.union` fvsMaybe k
    fvs (DimensionQuantifier l n) = fvs n
    fvs (DataQuantifier l v) = fvs v
    bvs (DomainQuantifier l n k) = bvs n `Set.union` bvsMaybe k
    bvs (DimensionQuantifier l n) = bvs n
    bvs (DataQuantifier l v) = bvs v

instance Vars (ProcedureDeclaration loc) where
    type VarOf (ProcedureDeclaration loc) = ScVar loc
    fvs (OperatorDeclaration l r op args s) = fvs r `Set.union` fvs op `Set.union` fvsFoldable args `Set.union` fvsFoldable s
    fvs (ProcedureDeclaration l r op args s) = fvs r `Set.union` fvs op `Set.union` fvsFoldable args `Set.union` fvsFoldable s
    bvs (OperatorDeclaration l r op args s) = bvs r `Set.union` bvs op `Set.union` bvsFoldable args `Set.union` bvsFoldable s
    bvs (ProcedureDeclaration l r op args s) = bvs r `Set.union` bvs op `Set.union` bvsFoldable args `Set.union` bvsFoldable s

instance Vars (Op loc) where
    type VarOf (Op loc) = ScVar loc
    fvs _ = Set.empty
    bvs _ = Set.empty

instance Vars (ReturnTypeSpecifier loc) where
    type VarOf (ReturnTypeSpecifier loc) = ScVar loc
    fvs (ReturnType l mb) = fvsMaybe mb
    bvs (ReturnType l mb) = bvsMaybe mb

instance Vars (ProcedureParameter loc) where
    type VarOf (ProcedureParameter loc) = ScVar loc
    fvs (ProcedureParameter l t v) = fvs t `Set.union` fvs v
    bvs (ProcedureParameter l t v) = bvs t `Set.union` bvs v

instance Vars (TypeSpecifier loc) where
    type VarOf (TypeSpecifier loc) = ScVar loc
    fvs (TypeSpecifier l s t d) = fvsMaybe s `Set.union` fvs t `Set.union` fvsMaybe d
    bvs (TypeSpecifier l s t d) = bvsMaybe s `Set.union` bvs t `Set.union` bvsMaybe d

instance Vars (ProcedureName loc) where
    type VarOf (ProcedureName loc) = ScVar loc
    fvs (ProcedureName l n) = Set.empty
    bvs (ProcedureName l n) = Set.empty

instance Vars (DimtypeSpecifier loc) where
    type VarOf (DimtypeSpecifier loc) = ScVar loc
    fvs (DimSpecifier l e) = fvs e
    bvs (DimSpecifier l e) = bvs e

instance Vars (SecTypeSpecifier loc) where
    type VarOf (SecTypeSpecifier loc) = ScVar loc
    fvs (PublicSpecifier l) = Set.empty
    fvs (PrivateSpecifier l d) = fvs d
    bvs (PublicSpecifier l) = Set.empty
    bvs (PrivateSpecifier l d) = bvs d

instance Vars (DatatypeSpecifier loc) where
    type VarOf (DatatypeSpecifier loc) = ScVar loc
    fvs (PrimitiveSpecifier l p) = fvs p
    fvs (TemplateSpecifier l t args) = fvs t `Set.union` fvsFoldable args
    fvs (VariableSpecifier l t) = fvs t
    bvs (PrimitiveSpecifier l p) = bvs p
    bvs (TemplateSpecifier l t args) = bvs t `Set.union` bvsFoldable args
    bvs (VariableSpecifier l t) = bvs t

instance Vars (TemplateTypeArgument loc) where
    type VarOf (TemplateTypeArgument loc) = ScVar loc
    fvs (GenericTemplateTypeArgument l n) = fvs n
    fvs (TemplateTemplateTypeArgument l t args) = fvs t `Set.union` fvsFoldable args
    fvs (PrimitiveTemplateTypeArgument l t) = fvs t
    fvs (IntTemplateTypeArgument l i) = Set.empty
    fvs (PublicTemplateTypeArgument l) = Set.empty
    bvs (GenericTemplateTypeArgument l n) = bvs n
    bvs (TemplateTemplateTypeArgument l t args) = bvs t `Set.union` bvsFoldable args
    bvs (PrimitiveTemplateTypeArgument l t) = bvs t
    bvs (IntTemplateTypeArgument l i) = Set.empty
    bvs (PublicTemplateTypeArgument l) = Set.empty

instance Vars (TypeName loc) where
    type VarOf (TypeName loc) = ScVar loc
    fvs (TypeName l n) = Set.empty
    bvs (TypeName l n) = Set.empty

instance Vars (TemplateArgName loc) where
    type VarOf (TemplateArgName loc) = ScVar loc
    fvs (TemplateArgName l n) = Set.empty
    bvs (TemplateArgName l n) = Set.empty

instance Vars (PrimitiveDatatype loc) where
    type VarOf (PrimitiveDatatype loc) = ScVar loc
    fvs t = Set.empty
    bvs t = Set.empty

fvsForInitializer :: ForInitializer loc -> Set (ScVar loc)
fvsForInitializer (InitializerExpression e) = fvsMaybe e
fvsForInitializer (InitializerVariable v) = fvs v

bvsForInitializer :: ForInitializer loc -> Set (ScVar loc)
bvsForInitializer (InitializerExpression e) = bvsMaybe e
bvsForInitializer (InitializerVariable v) = bvs v

instance Vars (SyscallParameter loc) where
    type VarOf (SyscallParameter loc) = ScVar loc
    fvs (SyscallPush _ e) = fvs e
    fvs (SyscallReturn _ v) = fvs v
    fvs (SyscallPushRef _ v) = fvs v
    fvs (SyscallPushCRef _ e) = fvs e
    bvs (SyscallPush _ e) = bvs e
    bvs (SyscallReturn _ v) = bvs v
    bvs (SyscallPushRef _ v) = bvs v
    bvs (SyscallPushCRef _ e) = bvs e
    
instance Vars (Statement loc) where
    type VarOf (Statement loc) = ScVar loc
    fvs (CompoundStatement _ ss) = fvsFoldable ss
    fvs (IfStatement _ e s1 s2) = fvs e `Set.union` fvs s1 `Set.union` fvsMaybe s2
    fvs (ForStatement _ i cond inc s) = fvsForInitializer i `Set.union` ((fvsMaybe cond `Set.union` fvsMaybe inc `Set.union` fvs s) `Set.difference` bvsForInitializer i)
    fvs (WhileStatement _ e s) = fvs e `Set.union` fvs s
    fvs (PrintStatement _ es) = Set.unions $ toList $ fmap fvs es
    fvs (DowhileStatement _ s e) = fvsBut s (fvs e)
    fvs (AssertStatement _ e) = fvs e
    fvs (SyscallStatement _ s ps) = Set.unions $ map fvs ps
    fvs (VarStatement _ d) = fvs d
    fvs (ReturnStatement _ e) = fvsMaybe e
    fvs (ContinueStatement _) = Set.empty
    fvs (BreakStatement _) = Set.empty
    fvs (ExpressionStatement _ e) = fvs e
    
    bvs (CompoundStatement _ ss) = bvsFoldable ss
    bvs (IfStatement _ e s1 s2) = bvs e `Set.union` bvs s1 `Set.union` bvsMaybe s2
    bvs (ForStatement _ i cond inc s) = bvsForInitializer i `Set.union` bvsMaybe cond `Set.union` bvsMaybe inc `Set.union` bvs s
    bvs (WhileStatement _ e s) = bvs e `Set.union` bvs s
    bvs (PrintStatement _ es) = Set.unions $ toList $ fmap bvs es
    bvs (DowhileStatement _ s e) = bvs s `Set.union` bvs e
    bvs (AssertStatement _ e) = bvs e
    bvs (SyscallStatement _ s ps) = Set.unions $ map bvs ps
    bvs (VarStatement _ d) = bvs d
    bvs (ReturnStatement _ e) = bvsMaybe e
    bvs (ContinueStatement _) = Set.empty
    bvs (BreakStatement _) = Set.empty
    bvs (ExpressionStatement _ e) = bvs e

instance Vars (VarName loc) where
    type VarOf (VarName loc) = ScVar loc
    fvs v = Set.singleton $ scVar v
    bvs = const Set.empty

scVar :: VarName loc -> ScVar loc
scVar (VarName l i) = ScVar l i

instance Vars (KindName loc) where
    type VarOf (KindName loc) = ScVar loc
    fvs (KindName l v) = Set.empty
    bvs = const Set.empty
    
instance Vars (DomainName loc) where
    type VarOf (DomainName loc) = ScVar loc
    fvs (DomainName l v) = Set.empty
    bvs = const Set.empty


-- | SecreC identifier kinds
data IdentifierType
    = DomainID
    | KindID
    | VarID
    | TypeID
    | ProcedureID
    | TemplateArgID -- domain, type or variable identifier
    | ModuleID
  deriving (Show,Read,Data,Typeable,Eq,Ord)
