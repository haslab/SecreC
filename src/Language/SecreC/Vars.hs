{-# LANGUAGE TypeFamilies, MultiParamTypeClasses #-}

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

varNameId :: VarName loc -> Identifier
varNameId (VarName _ i) = i

idsOf :: IdentifierType -> Map (Identifier,IdentifierType) a -> Map Identifier a
idsOf ty xs = Map.foldrWithKey (\(i,ty') v m -> if ty == ty' then Map.insert i v m else m) Map.empty xs

class Vars a where
    -- | Free variables
    fvs :: a -> Map (Identifier,IdentifierType) (LocOf a)
    bvs :: a -> Map (Identifier,IdentifierType) (LocOf a)

instance Vars (Module loc) where
    fvs (Module _ _ p) = fvs p
    bvs (Module _ _ p) = bvs p

fvsFoldable :: (Foldable t,Vars a) => t a -> Map (Identifier,IdentifierType) (LocOf a)
fvsFoldable = foldr (\x s -> fvs x `Map.union` (s `Map.difference` bvs x)) Map.empty
bvsFoldable :: (Foldable t,Vars a) => t a -> Map (Identifier,IdentifierType) (LocOf a)
bvsFoldable = foldr (\x s -> fvs x `Map.union` s) Map.empty

fvsBut x y = fvs x `Map.union` (y `Map.difference` bvs x)

fvsMaybe :: Vars a => Maybe a -> Map (Identifier,IdentifierType) (LocOf a)
fvsMaybe = maybe Map.empty fvs
bvsMaybe :: Vars a => Maybe a -> Map (Identifier,IdentifierType) (LocOf a)
bvsMaybe = maybe Map.empty bvs

instance Vars (Program loc) where
    fvs (Program _ _ gds) = fvsFoldable gds
    bvs (Program _ _ gds) = bvsFoldable gds
    
instance Vars (GlobalDeclaration loc) where
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
    fvs (VariableInitialization l v dim e) = ((maybe Map.empty fvs dim) `Map.union` (maybe Map.empty fvs e)) `Map.difference` fvs v
    bvs (VariableInitialization l v dim e) = bvs v 

instance Vars (Sizes loc) where
    fvs (Sizes xs) = foldr (\e u -> fvs e `Map.union` u) Map.empty xs
    bvs (Sizes xs) = foldr (\e u -> bvs e `Map.union` u) Map.empty xs

instance Vars (Expression loc) where
    fvs (BinaryAssign _ e1 op e2) = fvs e1 `Map.union` fvs e2
    fvs (QualifiedAssignExpr _ q) = fvs q
    bvs (BinaryAssign _ e1 op e2) = bvs e1 `Map.union` bvs e2
    bvs (QualifiedAssignExpr _ q) = bvs q

instance Vars (PostfixExpression loc)

instance Vars (QualifiedExpression loc)

instance Vars (StructureDeclaration loc)

instance Vars (VariableDeclaration loc)

instance Vars (DomainDeclaration loc) where
    fvs (Domain _ d k) = fvs k
    bvs (Domain _ d k) = bvs d `Map.union` bvs k

instance Vars (KindDeclaration loc) where
    fvs (Kind _ k) = Map.empty
    bvs (Kind _ k) = fvs k

instance Vars (TemplateDeclaration loc)

instance Vars (ProcedureDefinition loc)

fvsForInitializer :: ForInitializer loc -> Map (Identifier,IdentifierType) loc
fvsForInitializer (InitializerExpression e) = fvsMaybe e
fvsForInitializer (InitializerVariable v) = fvs v

bvsForInitializer :: ForInitializer loc -> Map (Identifier,IdentifierType) loc
bvsForInitializer (InitializerExpression e) = bvsMaybe e
bvsForInitializer (InitializerVariable v) = bvs v

instance Vars (SyscallParameter loc) where
    fvs (SyscallPush _ e) = fvs e
    fvs (SyscallReturn _ v) = fvs v
    fvs (SyscallPushRef _ v) = fvs v
    fvs (SyscallPushCRef _ e) = fvs e
    bvs (SyscallPush _ e) = bvs e
    bvs (SyscallReturn _ v) = bvs v
    bvs (SyscallPushRef _ v) = bvs v
    bvs (SyscallPushCRef _ e) = bvs e
    
instance Vars (Statement loc) where
    fvs (CompoundStatement _ ss) = fvsFoldable ss
    fvs (IfStatement _ e s1 s2) = fvs e `Map.union` fvs s1 `Map.union` fvsMaybe s2
    fvs (ForStatement _ i cond inc s) = fvsForInitializer i `Map.union` ((fvsMaybe cond `Map.union` fvsMaybe inc `Map.union` fvs s) `Map.difference` bvsForInitializer i)
    fvs (WhileStatement _ e s) = fvs e `Map.union` fvs s
    fvs (PrintStatement _ es) = Map.unions $ map fvs es
    fvs (DowhileStatement _ s e) = fvsBut s (fvs e)
    fvs (AssertStatement _ e) = fvs e
    fvs (SyscallStatement _ s ps) = Map.unions $ map fvs ps
    fvs (VarStatement _ d) = fvs d
    fvs (ReturnStatement _ e) = fvsMaybe e
    fvs (ContinueStatement _) = Map.empty
    fvs (BreakStatement _) = Map.empty
    fvs (ExpressionStatement _ e) = fvs e
    
    bvs (CompoundStatement _ ss) = bvsFoldable ss
    bvs (IfStatement _ e s1 s2) = bvs e `Map.union` bvs s1 `Map.union` bvsMaybe s2
    bvs (ForStatement _ i cond inc s) = bvsForInitializer i `Map.union` bvsMaybe cond `Map.union` bvsMaybe inc `Map.union` bvs s
    bvs (WhileStatement _ e s) = bvs e `Map.union` bvs s
    bvs (PrintStatement _ es) = Map.unions $ map bvs es
    bvs (DowhileStatement _ s e) = bvs s `Map.union` bvs e
    bvs (AssertStatement _ e) = bvs e
    bvs (SyscallStatement _ s ps) = Map.unions $ map bvs ps
    bvs (VarStatement _ d) = bvs d
    bvs (ReturnStatement _ e) = bvsMaybe e
    bvs (ContinueStatement _) = Map.empty
    bvs (BreakStatement _) = Map.empty
    bvs (ExpressionStatement _ e) = bvs e

instance Vars (VarName loc) where
    fvs (VarName l v) = Map.singleton (v,VarID) l
    bvs = const Map.empty

instance Vars (KindName loc) where
    fvs (KindName l v) = Map.singleton (v,KindID) l
    bvs = const Map.empty
    
instance Vars (DomainName loc) where
    fvs (DomainName l v) = Map.singleton (v,DomainID) l
    bvs = const Map.empty


