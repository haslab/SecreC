{-# LANGUAGE FunctionalDependencies, UndecidableInstances, ConstraintKinds, FlexibleInstances, GADTs, ScopedTypeVariables, RankNTypes, DeriveFunctor, FlexibleContexts, DeriveDataTypeable, TypeFamilies, MultiParamTypeClasses #-}

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
import Data.Generics hiding (typeOf)
import Data.Monoid
import Data.Int
import Data.Word
import Data.IORef

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State (StateT(..),State(..),execState,evalState)
import qualified Control.Monad.State as State

type Substs iden m = forall b . (GenVar iden m,IsScVar iden,IsScVar b) => iden -> m (Maybe b)
newtype SubstsProxy iden m = SubstsProxy { unSubstsProxy :: forall b . (GenVar iden m,IsScVar iden,IsScVar b) => Proxy b -> iden -> m (Maybe b) }

emptySubstsProxy :: Monad m => SubstsProxy iden m
emptySubstsProxy = SubstsProxy $ \proxy b -> return Nothing

appendSubstsProxy :: Monad m => SubstsProxy iden m -> SubstsProxy iden m -> SubstsProxy iden m
appendSubstsProxy f g = SubstsProxy (\proxy i -> do
    mb <- (unSubstsProxy f) proxy i
    maybe ((unSubstsProxy g) proxy i) (return . Just) mb)

class Monad m => GenVar v m where
    genVar :: v -> m v

class (GenVar iden m,IsScVar iden,MonadIO m,IsScVar a) => Vars iden m a where
    
    traverseVars :: (forall b . Vars iden m b => b -> VarsM iden m b) -> a -> VarsM iden m a
    
    -- tries to cast a value of type @a@ into a substitution variable
    substL :: Typeable a => a -> m (Maybe iden)
    substL = substL' Proxy
        where
        substL' :: Proxy iden -> (a -> m (Maybe iden))
        substL' pl a = case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf a) of
            EqT -> return $ Just a
            NeqT -> return Nothing
    
    unSubstL :: Typeable a => a -> iden -> m a
    unSubstL a iden = case eqTypeOf (typeOfProxy $ proxyOf iden) (typeOfProxy $ proxyOf a) of
            EqT -> return iden
            NeqT -> return a
    
    substVarsM :: Vars iden m iden => Substs iden m -> a -> VarsM iden m a
    substVarsM f x = do
        mbiden <- State.lift $ substL x
        x' <- case mbiden of -- try to substitute first
            Nothing -> return x
            Just v -> do
                b <- isBound v
                if b 
                    then do
                        (_,_,(_,ss),_,_) <- State.get
                        let v' = maybe v id (Map.lookup v ss)
                        State.lift $ unSubstL x v'
                    else do
                        r <- State.lift $ f v
                        case r of
                            Nothing -> return x
                            Just s -> do
                                s' <- substVarsM f s -- recursive case on substitution
                                return s'
        traverseVars (substVarsM f) x' -- go recursively
    
    subst :: Vars iden m iden => String -> Substs iden m -> Bool -> Map iden iden -> a -> m a
    subst msg f substBounds ss x = do
        --liftIO $ putStrLn $ "subst " ++ show msg
        x <- State.evalStateT (substVarsM f x) (False,False,(substBounds,ss),Map.empty,Set.empty)
        --liftIO $ putStrLn $ "unSubsts " ++ show msg
        return x
    
    substProxy :: Vars iden m iden => String -> SubstsProxy iden m -> Bool -> Map iden iden -> a -> m a
    substProxy msg (SubstsProxy f) substBounds ss x = subst msg (f Proxy) substBounds ss x
        
    fvs :: a -> m (Map iden Bool)
    fvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (False,False,(False,Map.empty),Map.empty,Set.empty)
        return y
    bvs :: a -> m (Set iden)
    bvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (False,False,(False,Map.empty),Map.empty,Set.empty)
        return z
    
    varsM :: a -> VarsM iden m a
    varsM x = traverseVars varsM x

substsFromMap :: (Vars iden m r) => Map iden r -> Substs iden m
substsFromMap xs = let f = unSubstsProxy (substsProxyFromMap xs) in f Proxy

substsProxyFromMap :: (Vars iden m r) => Map iden r -> SubstsProxy iden m
substsProxyFromMap = substsProxyFromList . Map.toList

substsFromList :: (Vars iden m r) => [(iden,r)] -> Substs iden m
substsFromList xs = let f = unSubstsProxy (substsProxyFromList xs) in f Proxy

substsProxyFromList :: (Vars iden m r) => [(iden,r)] -> SubstsProxy iden m
substsProxyFromList [] = SubstsProxy (\proxy iden -> return Nothing)
substsProxyFromList ((x,y):xs) = SubstsProxy (\proxy iden -> case (eqTypeOf (typeOf y) (typeOfProxy proxy)) of
    EqT -> if x==iden then return (Just y) else (unSubstsProxy $ substsProxyFromList xs) proxy iden
    otherwise -> return Nothing)

isBound :: (GenVar iden m,IsScVar iden,Monad m) => iden -> VarsM iden m Bool
isBound v = do
    (_,lval,ss,fvs,bvs) <- State.get
    return $ v `Set.member` bvs

type VarsM iden m = StateT
    (Bool -- is left-hand side
    ,Bool -- is l-value
    ,(Bool,Map iden iden) -- bound substitutions
    ,Map iden Bool -- free vars (read=False or written=True)
    ,Set iden)-- bound vars
    m

type IsScVar a = (Data a,Show a,PP a,Eq a,Ord a,Typeable a)

getLHS :: Monad m => VarsM iden m Bool
getLHS = liftM (\(x,lval,ss,y,z) -> x) State.get

inLHS :: Monad m => VarsM iden m a -> VarsM iden m a
inLHS m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(_,lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (True,lval,ss,fvs,bvs)
    State.put (lhs,lval',ss',fvs',bvs')
    return x

inLVal :: Monad m => VarsM iden m a -> VarsM iden m a
inLVal m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(lhs',_,ss',fvs',bvs')) <- State.lift $ State.runStateT m (lhs,True,ss,fvs,bvs)
    State.put (lhs',lval,ss',fvs',bvs')
    return x

inRHS :: Monad m => VarsM iden m a -> VarsM iden m a
inRHS m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(_,lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (False,lval,ss,fvs,bvs)
    State.put (lhs,lval',ss',fvs',bvs')
    return x

varsBlock :: (GenVar iden m,IsScVar iden,Monad m) => VarsM iden m a -> VarsM iden m a
varsBlock m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(lhs',lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (lhs,lval,ss,fvs,bvs)
    State.put (lhs',lval',ss,fvs',bvs) -- forget bound substitutions and bound variables
    return x

addFV :: (GenVar iden m,IsScVar iden,MonadIO m) => iden -> VarsM iden m ()
addFV x = State.modify $ \(lhs,lval,ss,fvs,bvs) -> if Set.member x bvs
    then (lhs,lval,ss,fvs,bvs) -- don't add an already bound variable to the free variables
    else (lhs,lval,ss,Map.insertWith (||) x lval fvs,bvs)
 
addBV :: (GenVar iden m,IsScVar iden,MonadIO m) => iden -> VarsM iden m ()
addBV x = do
    (lhs,lval,(substBounds,ss),fvs,bvs) <- State.get
    ss' <- if substBounds then liftM (\x' -> Map.insert x x' ss) (State.lift $ genVar x) else return ss
    State.put (lhs,lval,(substBounds,ss'),fvs,Set.insert x bvs)

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Integer where
    traverseVars f i = return i

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m [Char] where
    traverseVars f s = return s
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Int8 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Int16 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Int32 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Int64 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Double where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Float where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Int where
    traverseVars f i = return i

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Word8 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Word16 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Word32 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Word64 where
    traverseVars f i = return i

instance (PP a,PP b) => PP (Map a b) where
    pp xs = vcat $ map (\(k,v) -> pp k <+> char '=' <+> pp v) $ Map.toList xs

instance PP a => PP (Set a) where
    pp xs = sepBy space $ map pp $ Set.toList xs

instance (Vars iden m a,Vars iden m b) => Vars iden m (Map a b) where
    traverseVars f xs = liftM Map.fromList $ aux $ Map.toList xs
        where
        aux [] = return []
        aux ((k,v):xs) = do
            k' <- f k
            v' <- f v
            xs' <- aux xs
            return ((k',v'):xs')

instance Vars iden m a => Vars iden m (Set a) where
    traverseVars f xs = liftM Set.fromList $ mapM f $ Set.toList xs

instance Vars iden m a => Vars iden m (Maybe a) where
    traverseVars f x = mapM f x

instance (PP a,PP b) => PP (a,b) where
    pp (x,y) = pp x <+> pp y

instance (PP a,PP b,PP c) => PP (a,b,c) where
    pp (x,y,z) = pp x <+> pp y <+> pp z
   
instance (Vars iden m a,Vars iden m b) => Vars iden m (a,b) where
    traverseVars f (x,y) = do
        x' <- f x
        y' <- f y
        return (x',y')

instance (Vars iden m a,Vars iden m b,Vars iden m c) => Vars iden m (a,b,c) where
    traverseVars f (x,y,z) = do
        x' <- f x
        y' <- f y
        z' <- f z
        return (x',y',z')
    
instance (PP a,PP b) => PP (Either a b) where
    pp = either pp pp
    
instance (Vars iden m a,Vars iden m b) => Vars iden m (Either a b) where
    traverseVars f (Left x) = liftM Left $ f x
    traverseVars f (Right y) = liftM Right $ f y

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m () where
    traverseVars f () = return ()

instance (Vars iden m iden,Location loc,IsScVar iden,Vars iden m loc) => Vars iden m (ProcedureDeclaration iden loc) where
    traverseVars f (OperatorDeclaration l t o args anns s) = do
        l' <- f l
        t' <- f t
        o' <- f o
        varsBlock $ do
            args' <- mapM f args
            anns' <- mapM f anns
            s' <- mapM f s
            return $ OperatorDeclaration l' t' o' args' anns' s'
    traverseVars f (ProcedureDeclaration l t n args anns s) = do
        l' <- f l
        t' <- f t
        n' <- inLHS $ f n
        varsBlock $ do
            args' <- mapM f args
            anns' <- mapM f anns
            s' <- mapM f s
            return $ ProcedureDeclaration l' t' n' args' anns' s'

instance (Vars iden m iden,Location loc,IsScVar iden,Vars iden m loc) => Vars iden m (ProcedureParameter iden loc) where
    traverseVars f (ProcedureParameter l b t v) = do
        l' <- f l
        b' <- f b
        t' <- f t
        v' <- inLHS $ f v
        return $ ProcedureParameter l' b' t' v'
    traverseVars f (ConstProcedureParameter l b t v e) = do
        l' <- f l
        b' <- f b
        t' <- f t
        v' <- inLHS $ f v
        e' <- f e
        return $ ConstProcedureParameter l' b' t' v' e'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (ReturnTypeSpecifier iden loc) where
    traverseVars f (ReturnType l mb) = do
        l' <- f l
        mb' <- mapM f mb
        return $ ReturnType l' mb'
    
instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (VarName iden loc) where
    traverseVars f v@(VarName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ VarName l' n'
    substL (VarName _ n) = return $ Just n
    
instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (ProcedureName iden loc) where
    traverseVars f v@(ProcedureName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ ProcedureName l' n'
    substL (ProcedureName _ n) = return $ Just n

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (DomainName iden loc) where
    traverseVars f v@(DomainName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ DomainName l' n'
    substL (DomainName _ n) = return $ Just n

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (KindName iden loc) where
    traverseVars f v@(KindName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ KindName l' n'
    substL (KindName _ n) = return $ Just n

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (ModuleName iden loc) where
    traverseVars f v@(ModuleName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ ModuleName l' n'
    substL (ModuleName _ n) = return $ Just n

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (TemplateArgName iden loc) where
    traverseVars f v@(TemplateArgName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ TemplateArgName l' n'
    substL (TemplateArgName _ n) = return $ Just n

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (AttributeName iden loc) where
    traverseVars f v@(AttributeName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ AttributeName l' n'
    substL (AttributeName _ n) = return $ Just n

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (TypeName iden loc) where
    traverseVars f v@(TypeName l n) = do
        l' <- inRHS $ f l
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        n' <- f n
        return $ TypeName l' n'
    substL (TypeName _ n) = return $ Just n

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (TypeSpecifier iden loc) where
    traverseVars f (TypeSpecifier l sec d dim) = do
        l' <- f l
        sec' <- mapM f sec
        d' <- f d
        dim' <- mapM f dim
        return $ TypeSpecifier l' sec' d' dim'

instance (Location loc,Vars iden m loc) => Vars iden m (PrimitiveDatatype loc) where
    traverseVars f p = do
        l' <- f (loc p)
        return $ updLoc p l'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m [Statement iden loc] where
    traverseVars f xs = mapM f xs

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (Statement iden loc) where
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
    traverseVars f (ForStatement l i e1 e2 anns s) = varsBlock $ do
        l' <- f l
        i' <- f i
        e1' <- mapM f e1
        e2' <- mapM f e2
        anns' <- mapM f anns
        s' <- varsBlock $ f s
        return $ ForStatement l' i' e1' e2' anns' s'
    traverseVars f (WhileStatement l e anns s) = do
        l' <- f l
        e' <- f e
        anns' <- mapM f anns
        s' <- varsBlock $ f s
        return $ WhileStatement l' e' anns' s'
    traverseVars f (PrintStatement l es) = do
        l' <- f l
        es' <- mapM f es
        return $ PrintStatement l' es'
    traverseVars f (DowhileStatement l anns s e) = varsBlock $ do
        l' <- f l
        anns' <- mapM f anns
        s' <- f s
        e' <- f e
        return $ DowhileStatement l' anns' s' e'
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
    traverseVars f (ConstStatement l vd) = do
        l' <- f l
        vd' <- f vd
        return $ ConstStatement l' vd'
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
    traverseVars f (AnnStatement l e) = do
        l' <- f l
        e' <- f e
        return $ AnnStatement l' e'
    
instance (Vars iden m iden,Location loc,IsScVar iden,Vars iden m loc) => Vars iden m (Op iden loc) where
    traverseVars f (OpCast l t) = do
        l' <- f l
        t' <- f t
        return $ OpCast l' t'
    traverseVars f o = do
        l' <- f (loc o)
        return $ updLoc o l'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (DimtypeSpecifier iden loc) where
    traverseVars f (DimSpecifier l e) = do
        l' <- f l
        e' <- f e
        return $ DimSpecifier l' e'

instance (Location loc,Vars iden m loc) => Vars iden m (BinaryAssignOp loc) where
    traverseVars f o = do
        l' <- f (loc o)
        return $ updLoc o l'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m [Expression iden loc] where
    traverseVars f = mapM f

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m [(Expression iden loc,IsVariadic)] where
    traverseVars f = mapM (mapFstM f)

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (Expression iden loc) where
    traverseVars f (LeakExpr l x) = do
        l' <- f l
        x' <- f x
        return $ LeakExpr l' x'
    traverseVars f (BinaryAssign l e1 o e2) = do
        l' <- f l
        e1' <- inLVal $ f e1
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
        e' <- inLVal $ f e
        return $ PreOp l' o' e'
    traverseVars f (PostOp l o e) = do
        l' <- f l
        o' <- f o
        e' <- inLVal $ f e
        return $ PostOp l' o' e'   
    traverseVars f (DomainIdExpr l t) = do
        l' <- f l
        t' <- f t
        return $ DomainIdExpr l' t'
    traverseVars f (VArraySizeExpr l e) = do
        l' <- f l
        e' <- f e
        return $ VArraySizeExpr l' e'
    traverseVars f (VArrayExpr l e sz) = do
        l' <- f l
        e' <- f e
        sz' <- f sz
        return $ VArrayExpr l' e' sz'
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
    traverseVars f (QuantifiedExpr l q vs e) = do
        l' <- f l
        q' <- f q
        varsBlock $ do
            vs' <- inLHS $ mapM f vs
            e' <- f e
            return $ QuantifiedExpr l' q' vs' e'
    
    substL (RVariablePExpr _ v) = return $ Just $ varNameId v
    substL e = return Nothing

instance (Location loc,Vars iden m loc) => Vars iden m (Quantifier loc) where
    traverseVars f q = do
        l' <- f (loc q)
        return $ updLoc q l'

instance (Location loc,Vars iden m loc) => Vars iden m (Literal loc) where
    traverseVars f lit = do
        l' <- f (loc lit)
        return $ updLoc lit l'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (Index iden loc) where
    traverseVars f (IndexSlice l e1 e2) = do
        l' <- f l
        e1' <- mapM f e1
        e2' <- mapM f e2
        return $ IndexSlice l' e1' e2'
    traverseVars f (IndexInt l e) = do
        l' <- f l
        e' <- f e
        return $ IndexInt l' e'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (CastType iden loc) where
    traverseVars f (CastPrim p) = do
        p' <- f p
        return $ CastPrim p'
    traverseVars f (CastTy t) = do
        t' <- f t
        return $ CastTy t'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (DatatypeSpecifier iden loc) where
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
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (TemplateTypeArgument iden loc) where
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
    
instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (SecTypeSpecifier iden loc) where
    traverseVars f (PublicSpecifier l) = do
        l' <- f l
        return $ PublicSpecifier l'
    traverseVars f (PrivateSpecifier l d) = do
        l' <- f l
        d' <- f d
        return $ PrivateSpecifier l' d'
    substL (PrivateSpecifier l (DomainName _ n)) = return $ Just n
    substL s = return Nothing

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (VariableDeclaration iden loc) where
    traverseVars f (VariableDeclaration l t is) = do
        l' <- f l
        t' <- f t
        is' <- mapM f is
        return $ VariableDeclaration l' t' is'
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (VariableInitialization iden loc) where
    traverseVars f (VariableInitialization l v sz e) = do
        l' <- f l
        v' <- inLHS $ f v
        sz' <- mapM f sz
        e' <- mapM f e
        return $ VariableInitialization l' v' sz' e'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (ConstDeclaration iden loc) where
    traverseVars f (ConstDeclaration l t is) = do
        l' <- f l
        t' <- f t
        is' <- mapM f is
        return $ ConstDeclaration l' t' is'
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (ConstInitialization iden loc) where
    traverseVars f (ConstInitialization l v sz e) = do
        l' <- f l
        v' <- inLHS $ f v
        sz' <- mapM f sz
        e' <- mapM f e
        return $ ConstInitialization l' v' sz' e'
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (Sizes iden loc) where
    traverseVars f (Sizes es) = do
        es' <- mapM f es
        return $ Sizes es'
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (SyscallParameter iden loc) where
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

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (ForInitializer iden loc) where
    traverseVars f (InitializerExpression e) = do
        e' <- mapM f e
        return $ InitializerExpression e'
    traverseVars f (InitializerVariable vd) = do
        vd' <- f vd
        return $ InitializerVariable vd'
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (Module iden loc) where
    traverseVars f (Module l n p) = do
        l' <- f l
        n' <- mapM f n
        p' <- f p
        return $ Module l' n' p'
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (Program iden loc) where
    traverseVars f (Program l is gs) = do
        l' <- f l
        is' <- mapM f is
        gs' <- mapM f gs
        return $ Program l' is' gs'
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (GlobalDeclaration iden loc) where
    traverseVars f (GlobalVariable l vd) = do
        l' <- f l
        vd' <- f vd
        return $ GlobalVariable l' vd'
    traverseVars f (GlobalConst l vd) = do
        l' <- f l
        vd' <- f vd
        return $ GlobalConst l' vd'
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
    traverseVars f (GlobalAnnotations l t) = do
        l' <- f l
        t' <- mapM f t
        return $ GlobalAnnotations l' t'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (TemplateDeclaration iden loc) where
    traverseVars f (TemplateStructureDeclaration l qs s) = do
        l' <- f l
        qs' <- mapM f qs
        s' <- f s
        return $ TemplateStructureDeclaration l qs' s'
    traverseVars f (TemplateStructureSpecialization l qs specs s) = do
        l' <- f l
        qs' <- mapM f qs
        specs' <- mapM f specs
        s' <- f s
        return $ TemplateStructureSpecialization l' qs' specs' s'
    traverseVars f (TemplateProcedureDeclaration l qs p) = do
        l' <- f l
        qs' <- inLHS $ mapM f qs
        p' <- f p
        return $ TemplateProcedureDeclaration l' qs' p'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (StructureDeclaration iden loc) where
    traverseVars f (StructureDeclaration l n as) = do
        l' <- f l
        n' <- inLHS $ f n
        as' <- mapM f as
        return $ StructureDeclaration l' n' as'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (Attribute iden loc) where
    traverseVars f (Attribute l t a) = do
        l' <- f l
        t' <- f t
        a' <- inLHS $ f a
        return $ Attribute l' t' a'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (TemplateQuantifier iden loc) where
    traverseVars f (DomainQuantifier l b d k) = do
        l' <- f l
        b' <- f b
        d' <- inLHS $ f d
        k' <- mapM f k
        return $ DomainQuantifier l' b' d' k'
    traverseVars f (DimensionQuantifier l b d e) = do
        l' <- f l
        b' <- f b
        d' <- inLHS $ f d
        e' <- f e
        return $ DimensionQuantifier l' b' d' e'
    traverseVars f (DataQuantifier l b t) = do
        l' <- f l
        b' <- f b
        t' <- inLHS $ f t
        return $ DataQuantifier l' b' t'

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (KindDeclaration iden loc) where
    traverseVars f (Kind l n) = do
        l' <- f l
        n' <- inLHS $ f n
        return $ Kind l' n'

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (DomainDeclaration iden loc) where
    traverseVars f (Domain l d k) = do
        l' <- f l
        d' <- inLHS $ f d
        k' <- f k
        return $ Domain l' d' k'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m [ImportDeclaration iden loc] where
    traverseVars f xs = mapM f xs

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m [GlobalDeclaration iden loc] where
    traverseVars f xs = mapM f xs

instance (Vars iden m iden,Vars iden m loc,IsScVar iden) => Vars iden m (ImportDeclaration iden loc) where
    traverseVars f (Import l m) = do
        l' <- f l
        m' <- f m
        return $ Import l' m'

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Position where
    traverseVars f p = return p

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Bool where
    traverseVars f b = return b

instance (Vars iden m a,MonadIO m) => Vars iden m (UniqRef a) where
    traverseVars f ref = do
        x <- liftIO $ readUniqRef ref
        x' <- f x
        liftIO $ newUniqRef x'

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m Ordering where
    traverseVars f x = return x

instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m SecrecError where
    traverseVars f x = return x
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (LoopAnnotation iden loc) where
    traverseVars f (DecreasesAnn l e) = do
        l' <- f l
        e' <- f e
        return $ DecreasesAnn l' e'
    traverseVars f (InvariantAnn l e) = do
        l' <- f l
        e' <- f e
        return $ InvariantAnn l' e'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (StatementAnnotation iden loc) where
    traverseVars f (AssertAnn l e) = do
        l' <- f l
        e' <- f e
        return $ AssertAnn l' e'
    traverseVars f (AssumeAnn l e) = do
        l' <- f l
        e' <- f e
        return $ AssumeAnn l' e'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (ProcedureAnnotation iden loc) where
    traverseVars f (RequiresAnn l e) = do
        l' <- f l
        e' <- f e
        return $ RequiresAnn l' e'
    traverseVars f (EnsuresAnn l e) = do
        l' <- f l
        e' <- f e
        return $ EnsuresAnn l' e'

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m [StatementAnnotation iden loc] where
    traverseVars f xs = mapM f xs
    
instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m [ProcedureAnnotation iden loc] where
    traverseVars f xs = mapM f xs

instance (Vars iden m iden,Location loc,Vars iden m loc,IsScVar iden) => Vars iden m (GlobalAnnotation iden loc) where
    traverseVars f (GlobalProcedureAnn l qs p) = do
        l' <- f l
        qs' <- inLHS $ mapM f qs
        p' <- f p
        return $ GlobalProcedureAnn l' qs' p'







    

