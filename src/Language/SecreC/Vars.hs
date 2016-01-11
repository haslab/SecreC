{-# LANGUAGE UndecidableInstances, ConstraintKinds, FlexibleInstances, GADTs, ScopedTypeVariables, RankNTypes, DeriveFunctor, FlexibleContexts, DeriveDataTypeable, TypeFamilies, MultiParamTypeClasses #-}

module Language.SecreC.Vars where

import Prelude hiding (foldr)

import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Utils
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Error

import Text.PrettyPrint as PP

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Data.Generics
import Data.Monoid
import Data.Int
import Data.Word
import Data.IORef

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State (StateT(..),State(..),execState,evalState)
import qualified Control.Monad.State as State

class (Monad m,IsScVar a) => Vars m a where
    
    traverseVars :: (forall b . Vars m b => b -> VarsM m b) -> a -> VarsM m a
    
    -- tries to cast a value of type @a@ into a substitution variable
    substL :: IsScVar l => Proxy l -> (a -> m (Maybe l))
    substL pl a = case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf a) of
        EqT -> return $ Just a
        NeqT -> return Nothing
    -- tries to cast a substitution expression into a value of type @a@
    substR :: Vars m r => Proxy a -> (r -> m (Maybe a))
    substR pa r = case eqTypeOf (typeOfProxy pa) (typeOfProxy $ proxyOf r) of
        EqT -> return $ Just r
        NeqT -> return Nothing
    
    substVarsM :: (IsScVar l,Vars m r) => (l -> m (Maybe r)) -> a -> VarsM m a
    substVarsM (f :: v -> m (Maybe s)) (x::a) = do
        slx <- State.lift $ substL (Proxy::Proxy v) x
        x' <- case slx of
            Nothing -> return x
            Just v -> isBound v >>= \b -> if b -- we don't substitute bound variables
                then return x
                else do
                    r <- State.lift $ f v
                    case r of
                        Nothing -> return x
                        Just s -> do
                            srs <- State.lift $ substR (Proxy::Proxy a) s
                            case srs of
                                Nothing -> return x
                                Just x' -> return x'
        traverseVars (substVarsM f) x'
    
    subst :: (IsScVar l,Vars m r) => (l -> m (Maybe r)) -> a -> m a
    subst f x = State.evalStateT (substVarsM f x) (False,Set.empty,Set.empty)
    
    substFromMap :: (IsScVar l,Vars m r) => Map l r -> a -> m a
    substFromMap xs = subst (substsFromMap xs)
    
    substFromList :: (IsScVar l,Vars m r) => [(l,r)] -> a -> m a
    substFromList xs = subst (substsFromList xs)
        
    fvs :: a -> m (Set ScVar)
    fvs a = do
        (x,y,z) <- State.execStateT (varsM a) (False,Set.empty,Set.empty)
        return y
    bvs :: a -> m (Set ScVar)
    bvs a = do
        (x,y,z) <- State.execStateT (varsM a) (False,Set.empty,Set.empty)
        return z
    
    varsM :: a -> VarsM m a
    varsM x = traverseVars varsM x

substsFromMap :: (IsScVar l,Vars m r) => Map l r -> (l -> m (Maybe r))
substsFromMap xs = substsFromList (Map.toList xs)

substsFromList :: (IsScVar l,Vars m r) => [(l,r)] -> (l -> m (Maybe r))
substsFromList [] = const $ return Nothing
substsFromList ((x,y):xs) = \l -> if l==x
    then return $ Just y
    else substsFromList xs l

isBound :: (Monad m,IsScVar v) => v -> VarsM m Bool
isBound v = do
    (_,fvs,bvs) <- State.get
    return $ (ScVar v) `Set.member` bvs

type VarsM m = StateT
    (Bool -- is left-hand side
    ,Set ScVar -- free vars
    ,Set ScVar)-- bound vars
    m

data ScVar where
    ScVar :: IsScVar a => a -> ScVar

instance Show ScVar where
    show (ScVar x) = show x
instance Eq ScVar where
    (ScVar x) == (ScVar y) = case eqTypeOf (typeOfProxy $ proxyOf x) (typeOfProxy $ proxyOf y) of
        EqT -> x == y
        NeqT -> False
instance Ord ScVar where
    compare (ScVar x) (ScVar y) = case eqTypeOf (typeOfProxy $ proxyOf x) (typeOfProxy $ proxyOf y) of
        EqT -> compare x y
        NeqT -> compare (typeOf x) (typeOf y)

type IsScVar a = (Data a,Show a,PP a,Eq a,Ord a,Typeable a)

getLHS :: Monad m => VarsM m Bool
getLHS = liftM (\(x,y,z) -> x) State.get

inLHS :: Monad m => VarsM m a -> VarsM m a
inLHS m = do
    (lhs,fvs,bvs) <- State.get
    (x,(_,fvs',bvs')) <- State.lift $ State.runStateT m (True,fvs,bvs)
    State.put (lhs,fvs',bvs')
    return x

inRHS :: Monad m => VarsM m a -> VarsM m a
inRHS m = do
    (lhs,fvs,bvs) <- State.get
    (x,(_,fvs',bvs')) <- State.lift $ State.runStateT m (False,fvs,bvs)
    State.put (lhs,fvs',bvs')
    return x

varsBlock :: Monad m => VarsM m a -> VarsM m a
varsBlock m = do
    (lhs,fvs,bvs) <- State.get
    (x,(lhs',fvs',bvs')) <- State.lift $ State.runStateT m (lhs,fvs,bvs)
    State.put (lhs',fvs',bvs) -- forget bound variables
    return x

addFV :: (Monad m,Functor a,IsScVar (a ()),IsScVar (a loc)) => a loc -> VarsM m ()
addFV x = State.modify $ \(lhs,fvs,bvs) -> if Set.member (ScVar c) bvs
    then (lhs,fvs,bvs) -- don't add an already bound variable to the free variables
    else (lhs,Set.insert (ScVar c) fvs,bvs)
 where c = funit x

addBV :: (Monad m,Functor a,IsScVar (a ()),IsScVar (a loc)) => a loc -> VarsM m ()
addBV x = State.modify $ \(lhs,fvs,bvs) -> (lhs,fvs,Set.insert (ScVar c) bvs)
 where c = funit x

addFVId :: (Monad m,IsScVar a) => a -> VarsM m ()
addFVId x = State.modify $ \(lhs,fvs,bvs) -> if Set.member (ScVar x) bvs
    then (lhs,fvs,bvs) -- don't add an already bound variable to the free variables
    else (lhs,Set.insert (ScVar x) fvs,bvs)
 
addBVId :: (Monad m,IsScVar a) => a -> VarsM m ()
addBVId x = State.modify $ \(lhs,fvs,bvs) -> (lhs,fvs,Set.insert (ScVar x) bvs)

instance Monad m => Vars m Integer where
    traverseVars f i = return i
    
instance Monad m => Vars m Int64 where
    traverseVars f i = return i
    
instance Monad m => Vars m Word64 where
    traverseVars f i = return i

instance (PP a,PP b) => PP (Map a b) where
    pp xs = vcat $ map (\(k,v) -> pp k <+> char '=' <+> pp v) $ Map.toList xs

instance PP a => PP (Set a) where
    pp xs = vcat $ map pp $ Set.toList xs

instance (Vars m a,Vars m b) => Vars m (Map a b) where
    traverseVars f xs = liftM Map.fromList $ aux $ Map.toList xs
        where
        aux [] = return []
        aux ((k,v):xs) = do
            k' <- inLHS $ f k
            v' <- f v
            xs' <- aux xs
            return ((k',v'):xs')

instance Vars m a => Vars m (Set a) where
    traverseVars f xs = liftM Set.fromList $ mapM f $ Set.toList xs

instance Vars m a => Vars m (Maybe a) where
    traverseVars f x = mapM f x

instance (PP a,PP b) => PP (a,b) where
    pp (x,y) = pp x <+> pp y
   
instance (Vars m a,Vars m b) => Vars m (a,b) where
    traverseVars f (x,y) = do
        x' <- f x
        y' <- f y
        return (x',y')
    
instance (PP a,PP b) => PP (Either a b) where
    pp = either pp pp
    
instance (Vars m a,Vars m b) => Vars m (Either a b) where
    traverseVars f (Left x) = liftM Left $ f x
    traverseVars f (Right y) = liftM Right $ f y

instance Monad m => Vars m () where
    traverseVars f () = return ()

instance (Location loc,IsScVar iden,Vars m loc) => Vars m (ProcedureDeclaration iden loc) where
    traverseVars f (OperatorDeclaration l t o args s) = do
        l' <- f l
        t' <- f t
        o' <- f o
        varsBlock $ do
            args' <- inLHS $ mapM f args
            s' <- mapM f s
            return $ OperatorDeclaration l' t' o' args' s'
    traverseVars f (ProcedureDeclaration l t n args s) = do
        l' <- f l
        t' <- f t
        n' <- inLHS $ f n
        varsBlock $ do
            args' <- inLHS $ mapM f args
            s' <- mapM f s
            return $ ProcedureDeclaration l' t' n' args' s'

instance (Location loc,IsScVar iden,Vars m loc) => Vars m (ProcedureParameter iden loc) where
    traverseVars f (ProcedureParameter l t v sz e) = do
        l' <- f l
        t' <- f t
        v' <- f v
        sz' <- f sz
        e' <- f e
        return $ ProcedureParameter l' t' v' sz' e'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (ReturnTypeSpecifier iden loc) where
    traverseVars f (ReturnType l mb) = do
        l' <- f l
        mb' <- mapM f mb
        return $ ReturnType l' mb'
    
instance (Vars m loc,IsScVar iden) => Vars m (VarName iden loc) where
    traverseVars f v@(VarName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ VarName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing
    
instance (Vars m loc,IsScVar iden) => Vars m (ProcedureName iden loc) where
    traverseVars f v@(ProcedureName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ ProcedureName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing

instance (Vars m loc,IsScVar iden) => Vars m (DomainName iden loc) where
    traverseVars f v@(DomainName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ DomainName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing

instance (Vars m loc,IsScVar iden) => Vars m (KindName iden loc) where
    traverseVars f v@(KindName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ KindName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing

instance (Vars m loc,IsScVar iden) => Vars m (ModuleName iden loc) where
    traverseVars f v@(ModuleName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ ModuleName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing

instance (Vars m loc,IsScVar iden) => Vars m (TemplateArgName iden loc) where
    traverseVars f v@(TemplateArgName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ TemplateArgName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing

instance (Vars m loc,IsScVar iden) => Vars m (AttributeName iden loc) where
    traverseVars f v@(AttributeName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ AttributeName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing

instance (Vars m loc,IsScVar iden) => Vars m (TypeName iden loc) where
    traverseVars f v@(TypeName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV v else addFV v
        return $ TypeName l' n
    substL pl v = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (TypeSpecifier iden loc) where
    traverseVars f (TypeSpecifier l sec d dim) = do
        l' <- f l
        sec' <- mapM f sec
        d' <- f d
        dim' <- mapM f dim
        return $ TypeSpecifier l' sec' d' dim'

instance (Location loc,Vars m loc) => Vars m (PrimitiveDatatype loc) where
    traverseVars f p = do
        l' <- f (loc p)
        return $ updLoc p l'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m [Statement iden loc] where
    traverseVars f xs = mapM f xs

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (Statement iden loc) where
    traverseVars f (CompoundStatement l ss) = varsBlock $ do
        l' <- f l
        ss' <- mapM f ss
        return $ CompoundStatement l' ss'
    traverseVars f (IfStatement l e s1 s2) = do
        l' <- f l
        e' <- f e
        s1' <- varsBlock $ f s1
        s2' <- varsBlock $ mapM f s2
        return $ IfStatement l' e' s1' s2'
    traverseVars f (ForStatement l i e1 e2 s) = varsBlock $ do
        l' <- f l
        i' <- f i
        e1' <- mapM f e1
        e2' <- mapM f e2
        s' <- varsBlock $ f s
        return $ ForStatement l' i' e1' e2' s'
    traverseVars f (WhileStatement l e s) = do
        l' <- f l
        e' <- f e
        s' <- varsBlock $ f s
        return $ WhileStatement l' e' s'
    traverseVars f (PrintStatement l es) = do
        l' <- f l
        es' <- mapM f es
        return $ PrintStatement l' es'
    traverseVars f (DowhileStatement l s e) = varsBlock $ do
        l' <- f l
        s' <- f s
        e' <- f e
        return $ DowhileStatement l' s' e'
    traverseVars f (AssertStatement l e) = do
        l' <- f l
        e' <- f e
        return $ AssertStatement l' e'
    traverseVars f (SyscallStatement l str ps) = do
        l' <- f l
        ps' <- mapM f ps
        return $ SyscallStatement l' str ps'
    traverseVars f (VarStatement l vd) = do
        l' <- f l
        vd' <- f vd
        return $ VarStatement l' vd'
    traverseVars f (ReturnStatement l e) = do
        l' <- f l
        e' <- mapM f e
        return $ ReturnStatement l' e'
    traverseVars f (ContinueStatement l) = do
        l' <- f l
        return $ ContinueStatement l'
    traverseVars f (BreakStatement l) = do
        l' <- f l
        return $ BreakStatement l'
    traverseVars f (ExpressionStatement l e) = do
        l' <- f l
        e' <- f e
        return $ ExpressionStatement l' e'
    
instance (Location loc,IsScVar iden,Vars m loc) => Vars m (Op iden loc) where
    traverseVars f (OpCast l t) = do
        l' <- f l
        t' <- f t
        return $ OpCast l' t'
    traverseVars f o = do
        l' <- f (loc o)
        return $ updLoc o l'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (DimtypeSpecifier iden loc) where
    traverseVars f (DimSpecifier l e) = do
        l' <- f l
        e' <- f e
        return $ DimSpecifier l' e'

instance (Location loc,Vars m loc) => Vars m (BinaryAssignOp loc) where
    traverseVars f o = do
        l' <- f (loc o)
        return $ updLoc o l'

-- Supported expression substitutions:
-- VarName iden () --> VarName iden loc
-- VarName iden () --> Expression iden loc
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (Expression iden loc) where
    traverseVars f (BinaryAssign l e1 o e2) = do
        l' <- f l
        e1' <- f e1
        o' <- f o
        e2' <- f e2
        return $ BinaryAssign l' e1' o' e2'
    traverseVars f (QualExpr l e t) = do
        l' <- f l
        e' <- f e
        t' <- f t
        return $ QualExpr l' e' t'
    traverseVars f (CondExpr l e1 e2 e3) = do
        l' <- f l
        e1' <- f e1
        e2' <- f e2
        e3' <- f e3
        return $ CondExpr l' e1' e2' e3'
    traverseVars f (BinaryExpr l e1 o e2) = do
        l' <- f l
        e1' <- f e1
        o' <- f o
        e2' <- f e2
        return $ BinaryExpr l' e1' o' e2'
    traverseVars f (UnaryExpr l o e) = do
        l' <- f l
        o' <- f o
        e' <- f e
        return $ UnaryExpr l' o' e'
    traverseVars f (PreOp l o e) = do
        l' <- f l
        o' <- f o
        e' <- f e
        return $ PreOp l' o' e'
    traverseVars f (PostOp l o e) = do
        l' <- f l
        o' <- f o
        e' <- f e
        return $ PostOp l' o' e'   
    traverseVars f (DomainIdExpr l t) = do
        l' <- f l
        t' <- f t
        return $ DomainIdExpr l' t'
    traverseVars f (BytesFromStringExpr l e) = do
        l' <- f l
        e' <- f e
        return $ BytesFromStringExpr l' e'
    traverseVars f (StringFromBytesExpr l e) = do
        l' <- f l
        e' <- f e
        return $ StringFromBytesExpr l' e'
    traverseVars f (ProcCallExpr l n ts es) = do
        l' <- f l
        n' <- f n
        ts' <- mapM (mapM f) ts
        es' <- mapM f es
        return $ ProcCallExpr l' n' ts' es'
    traverseVars f (PostIndexExpr l e s) = do
        l' <- f l
        e' <- f e
        s' <- mapM f s
        return $ PostIndexExpr l' e' s'
    traverseVars f (SelectionExpr l e a) = do
        l' <- f l
        e' <- f e
        a' <- f a
        return $ SelectionExpr l' e' a'
    traverseVars f (ArrayConstructorPExpr l es) = do
        l' <- f l
        es' <- mapM f es
        return $ ArrayConstructorPExpr l' es'
    traverseVars f (RVariablePExpr l v) = do
        l' <- f l
        v' <- f v
        return $ RVariablePExpr l' v'
    traverseVars f (LitPExpr l lit) = do
        l' <- f l
        lit' <- f lit
        return $ LitPExpr l' lit'
    
    substL pl (RVariablePExpr _ v) = let n = funit v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing
    substL pl e = return Nothing
    substR (pa::Proxy (Expression iden loc)) r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy (Proxy::Proxy (VarName iden loc))) of
            EqT -> return $ Just (RVariablePExpr (loc r) r)
            NeqT -> case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
                EqT -> return $ Just r
                NeqT -> return Nothing

instance (Location loc,Vars m loc) => Vars m (Literal loc) where
    traverseVars f lit = do
        l' <- f (loc lit)
        return $ updLoc lit l'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (Index iden loc) where
    traverseVars f (IndexSlice l e1 e2) = do
        l' <- f l
        e1' <- mapM f e1
        e2' <- mapM f e2
        return $ IndexSlice l' e1' e2'
    traverseVars f (IndexInt l e) = do
        l' <- f l
        e' <- f e
        return $ IndexInt l' e'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (CastType iden loc) where
    traverseVars f (CastPrim p) = do
        p' <- f p
        return $ CastPrim p'
    traverseVars f (CastTy t) = do
        t' <- f t
        return $ CastTy t'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (DatatypeSpecifier iden loc) where
    traverseVars f (PrimitiveSpecifier l p) = do
        l' <- f l
        p' <- f p
        return $ PrimitiveSpecifier l' p'
    traverseVars f (TemplateSpecifier l t args) = do
        l' <- f l
        t' <- f t
        args' <- mapM f args
        return $ TemplateSpecifier l' t' args'
    traverseVars f (VariableSpecifier l t) = do
        l' <- f l
        t' <- f t
        return $ VariableSpecifier l' t'
    
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (TemplateTypeArgument iden loc) where
    traverseVars f (GenericTemplateTypeArgument l n) = do
        l' <- f l
        n' <- f n
        return $ GenericTemplateTypeArgument l' n'
    traverseVars f (TemplateTemplateTypeArgument l n args) = do
        l' <- f l
        n' <- f n
        args' <- mapM f args
        return $ TemplateTemplateTypeArgument l' n' args'
    traverseVars f (PrimitiveTemplateTypeArgument l p) = do
        l' <- f l
        p' <- f p
        return $ PrimitiveTemplateTypeArgument l' p'
    traverseVars f (ExprTemplateTypeArgument l i) = do
        l' <- f l
        return $ ExprTemplateTypeArgument l' i
    traverseVars f (PublicTemplateTypeArgument l) = do
        l' <- f l
        return $ PublicTemplateTypeArgument l'
    
instance (Vars m loc,IsScVar iden) => Vars m (SecTypeSpecifier iden loc) where
    traverseVars f (PublicSpecifier l) = do
        l' <- f l
        return $ PublicSpecifier l'
    traverseVars f (PrivateSpecifier l d) = do
        l' <- f l
        d' <- f d
        return $ PrivateSpecifier l' d'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (VariableDeclaration iden loc) where
    traverseVars f (VariableDeclaration l t is) = do
        l' <- f l
        t' <- f t
        is' <- mapM f is
        return $ VariableDeclaration l' t' is'
    
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (VariableInitialization iden loc) where
    traverseVars f (VariableInitialization l v sz e c) = do
        l' <- f l
        v' <- inLHS $ f v
        sz' <- mapM f sz
        e' <- mapM f e
        c' <- mapM f c
        return $ VariableInitialization l' v' sz' e' c'
    
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (Sizes iden loc) where
    traverseVars f (Sizes es) = do
        es' <- mapM f es
        return $ Sizes es'
    
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (SyscallParameter iden loc) where
    traverseVars f (SyscallPush l e) = do
        l' <- f l
        e' <- f e
        return $ SyscallPush l' e'
    traverseVars f (SyscallReturn l v) = do
        l' <- f l
        v' <- f v
        return $ SyscallReturn l' v'
    traverseVars f (SyscallPushRef l v) = do
        l' <- f l
        v' <- f v
        return $ SyscallPushRef l' v'
    traverseVars f (SyscallPushCRef l e) = do
        l' <- f l
        e' <- f e
        return $ SyscallPushCRef l' e'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (ForInitializer iden loc) where
    traverseVars f (InitializerExpression e) = do
        e' <- mapM f e
        return $ InitializerExpression e'
    traverseVars f (InitializerVariable vd) = do
        vd' <- f vd
        return $ InitializerVariable vd'
    
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (Module iden loc) where
    traverseVars f (Module l n p) = do
        l' <- f l
        n' <- mapM f n
        p' <- f p
        return $ Module l' n' p'
    
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (Program iden loc) where
    traverseVars f (Program l is gs) = do
        l' <- f l
        is' <- mapM f is
        gs' <- mapM f gs
        return $ Program l' is' gs'
    
instance (Location loc,Vars m loc,IsScVar iden) => Vars m (GlobalDeclaration iden loc) where
    traverseVars f (GlobalVariable l vd) = do
        l' <- f l
        vd' <- f vd
        return $ GlobalVariable l' vd'
    traverseVars f (GlobalDomain l d) = do
        l' <- f l
        d' <- f d
        return $ GlobalDomain l' d'
    traverseVars f (GlobalKind l k) = do
        l' <- f l
        k' <- f k
        return $ GlobalKind l' k'
    traverseVars f (GlobalProcedure l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalProcedure l' p'
    traverseVars f (GlobalStructure l s) = do
        l' <- f l
        s' <- f s
        return $ GlobalStructure l' s'
    traverseVars f (GlobalTemplate l t) = do
        l' <- f l
        t' <- f t
        return $ GlobalTemplate l' t'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (TemplateDeclaration iden loc) where
    traverseVars f (TemplateStructureDeclaration l qs s) = do
        l' <- f l
        qs' <- inLHS $ mapM f qs
        s' <- f s
        return $ TemplateStructureDeclaration l qs' s'
    traverseVars f (TemplateStructureSpecialization l qs specs s) = do
        l' <- f l
        qs' <- inLHS $ mapM f qs
        specs' <- mapM f specs
        s' <- f s
        return $ TemplateStructureSpecialization l' qs' specs' s'
    traverseVars f (TemplateProcedureDeclaration l qs p) = do
        l' <- f l
        qs' <- inLHS $ mapM f qs
        p' <- f p
        return $ TemplateProcedureDeclaration l' qs' p'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (StructureDeclaration iden loc) where
    traverseVars f (StructureDeclaration l n as) = do
        l' <- f l
        n' <- inLHS $ f n
        as' <- mapM f as
        return $ StructureDeclaration l' n' as'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (Attribute iden loc) where
    traverseVars f (Attribute l t a) = do
        l' <- f l
        t' <- f t
        a' <- inLHS $ f a
        return $ Attribute l' t' a'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m (TemplateQuantifier iden loc) where
    traverseVars f (DomainQuantifier l d k) = do
        l' <- f l
        d' <- inLHS $ f d
        k' <- mapM f k
        return $ DomainQuantifier l' d' k'
    traverseVars f (DimensionQuantifier l d e) = do
        l' <- f l
        d' <- inLHS $ f d
        e' <- f e
        return $ DimensionQuantifier l' d' e'
    traverseVars f (DataQuantifier l t) = do
        l' <- f l
        t' <- inLHS $ f t
        return $ DataQuantifier l' t'

instance (Vars m loc,IsScVar iden) => Vars m (KindDeclaration iden loc) where
    traverseVars f (Kind l n) = do
        l' <- f l
        n' <- inLHS $ f n
        return $ Kind l' n'

instance (Vars m loc,IsScVar iden) => Vars m (DomainDeclaration iden loc) where
    traverseVars f (Domain l d k) = do
        l' <- f l
        d' <- inLHS $ f d
        k' <- f k
        return $ Domain l' d' k'

instance (Location loc,Vars m loc,IsScVar iden) => Vars m [ImportDeclaration iden loc] where
    traverseVars f xs = mapM f xs

instance (Location loc,Vars m loc,IsScVar iden) => Vars m [GlobalDeclaration iden loc] where
    traverseVars f xs = mapM f xs

instance (Vars m loc,IsScVar iden) => Vars m (ImportDeclaration iden loc) where
    traverseVars f (Import l m) = do
        l' <- f l
        m' <- f m
        return $ Import l' m'

instance Monad m => Vars m Position where
    traverseVars f p = return p

instance Monad m => Vars m Bool where
    traverseVars f b = return b

instance (Vars m a,MonadIO m) => Vars m (UniqRef a) where
    traverseVars f ref = do
        x <- liftIO $ readUniqRef ref
        x' <- f x
        liftIO $ newUniqRef x'

instance Monad m => Vars m Ordering where
    traverseVars f x = return x

instance Monad m => Vars m SecrecError where
    traverseVars f x = return x




