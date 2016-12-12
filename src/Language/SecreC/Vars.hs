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

type Stop m = forall a . (IsScVar m a) => a -> m Bool
newtype StopProxy m = StopProxy { unStopProxy :: forall a . (IsScVar m a) => Proxy a -> a -> m Bool }

dontStop :: StopProxy m
dontStop = StopProxy $ \_ x -> return False

type Substs iden m = forall b . (GenVar iden m,IsScVar m iden,IsScVar m b) => iden -> m (Maybe b)
newtype SubstsProxy iden m = SubstsProxy { unSubstsProxy :: forall b . (GenVar iden m,IsScVar m iden,IsScVar m b) => Proxy b -> iden -> m (Maybe b) }

emptySubstsProxy :: Monad m => SubstsProxy iden m
emptySubstsProxy = SubstsProxy $ \proxy b -> return Nothing

appendSubstsProxy :: Monad m => SubstsProxy iden m -> SubstsProxy iden m -> SubstsProxy iden m
appendSubstsProxy f g = SubstsProxy (\proxy i -> do
    mb <- (unSubstsProxy f) proxy i
    maybe ((unSubstsProxy g) proxy i) (return . Just) mb)

class Monad m => GenVar v m where
    genVar :: v -> m v
    mkVar :: String -> m v

class (GenVar iden m,IsScVar m iden,MonadIO m,IsScVar m a) => Vars iden m a where
    
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
    
    substVarsM :: Vars iden m iden => StopProxy m -> Substs iden m -> a -> VarsM iden m a
    substVarsM stp@(StopProxy stop) f x = do
        mbiden <- State.lift $ substL x
        x' <- case mbiden of -- try to substitute first
            Nothing -> return x
            Just v -> do
                b <- isBound v
                isLHS <- getLHS
                if (maybe False not b || maybe False not isLHS)
                    then do
                        --liftIO $ putStrLn $ "isBound " ++ ppr v
                        (_,_,(_,ss),_,_) <- State.get
                        let v' = maybe v id (Map.lookup v ss)
                        State.lift $ unSubstL x v'
                    else do
                        --liftIO $ putStrLn $ "isNotBound " ++ ppr v
                        r <- State.lift $ f v
                        case r of
                            Nothing -> return x
                            Just s -> do
                                --liftIO $ putStrLn $ "substituted " ++ ppr v ++ " --> " ++ ppr s
                                s' <- substVarsM stp f s -- go recursively in case of substitution
                                return s'
        ko <- State.lift $ stop Proxy x'
        if ko
            then return x'
            else traverseVars (substVarsM stp f) x' -- descend into children
    
    subst :: Vars iden m iden => String -> StopProxy m -> Substs iden m -> Bool -> Map iden iden -> a -> m a
    subst msg stop f substBounds ss x = do
        --liftIO $ putStrLn $ "subst " ++ show msg
        x <- State.evalStateT (substVarsM stop f x) (Nothing,False,(substBounds,ss),Map.empty,Map.empty)
        --liftIO $ putStrLn $ "unSubsts " ++ show msg
        return x
    
    substProxy :: Vars iden m iden => String -> StopProxy m -> SubstsProxy iden m -> Bool -> Map iden iden -> a -> m a
    substProxy msg stop (SubstsProxy f) substBounds ss x = subst msg stop (f Proxy) substBounds ss x
        
    fvs :: a -> m (Map iden Bool)
    fvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (Nothing,False,(False,Map.empty),Map.empty,Map.empty)
        return y
    bvs :: a -> m (Map iden Bool)
    bvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (Nothing,False,(False,Map.empty),Map.empty,Map.empty)
        return z
    uvs :: a -> m (Map iden Bool,Map iden Bool)
    uvs a = do
        (x,lval,s,y,z) <- State.execStateT (varsM a) (Nothing,False,(False,Map.empty),Map.empty,Map.empty)
        return (y,z)
    
    varsM :: a -> VarsM iden m a
    varsM x = traverseVars varsM x

fvsSet :: Vars iden m a => a -> m (Set iden)
fvsSet = liftM Map.keysSet . fvs

bvsSet :: Vars iden m a => a -> m (Set iden)
bvsSet = liftM Map.keysSet . bvs

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

isBound :: (GenVar iden m,IsScVar m iden,Monad m) => iden -> VarsM iden m (Maybe Bool)
isBound v = do
    (_,lval,ss,fvs,bvs) <- State.get
    return $ Map.lookup v bvs

type VarsM iden m = StateT
    (Maybe Bool -- is left-hand side
    ,Bool -- is l-value
    ,(Bool,Map iden iden) -- bound substitutions
    ,Map iden Bool -- free vars (read=False or written=True)
    ,Map iden Bool-- bound vars (variable=false or name=True)
    )
    m

type IsScVar m a = (Data a,Show a,PP m a,Eq a,Ord a,Typeable a)

getLHS :: Monad m => VarsM iden m (Maybe Bool)
getLHS = liftM (\(x,lval,ss,y,z) -> x) State.get

inLHS :: Monad m => Bool -> VarsM iden m a -> VarsM iden m a
inLHS isName m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(_,lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (Just isName,lval,ss,fvs,bvs)
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
    (x,(_,lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (Nothing,lval,ss,fvs,bvs)
    State.put (lhs,lval',ss',fvs',bvs')
    return x

varsBlock :: (GenVar iden m,IsScVar m iden,Monad m) => VarsM iden m a -> VarsM iden m a
varsBlock m = do
    (lhs,lval,ss,fvs,bvs) <- State.get
    (x,(lhs',lval',ss',fvs',bvs')) <- State.lift $ State.runStateT m (lhs,lval,ss,fvs,bvs)
    State.put (lhs',lval',ss,fvs',bvs) -- forget bound substitutions and bound variables
    return x

addFV :: (GenVar iden m,IsScVar m iden2,MonadIO m) => (iden -> iden2) -> iden -> VarsM iden2 m iden
addFV to x = do
    State.modify $ \(lhs,lval,ss,fvs,bvs) -> if isJust (Map.lookup (to x) bvs)
        then (lhs,lval,ss,fvs,bvs) -- don't add an already bound variable to the free variables
        else (lhs,lval,ss,Map.insertWith (||) (to x) lval fvs,bvs)
    return x
 
addBV :: (GenVar iden m,IsScVar m iden2,MonadIO m) => (iden -> iden2) -> iden -> VarsM iden2 m iden
addBV to x = do
    --liftIO $ putStrLn $ "addBV " ++ ppr x
    (lhs,lval,(substBounds,ss),fvs,bvs) <- State.get
    let isName = maybe False id lhs
    (x',ss') <- if not isName && substBounds then liftM (\x' -> (x',Map.insert (to x) (to x') ss)) (State.lift $ genVar x) else return (x,ss)
    State.put (lhs,lval,(substBounds,ss'),fvs,Map.insert (to x) isName bvs)
    return x'

instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Integer where
    traverseVars f i = return i

instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m [Char] where
    traverseVars f s = return s
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Int8 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Int16 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Int32 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Int64 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Double where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Float where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Int where
    traverseVars f i = return i

instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Word8 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Word16 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Word32 where
    traverseVars f i = return i
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m Word64 where
    traverseVars f i = return i

instance (PP m a,PP m b) => PP m (Map a b) where
    pp xs = do
        let f (k,v) = do
            ppk <- pp k
            ppv <- pp v
            return $ ppk <+> char '=' <+> ppv
        liftM vcat $ mapM f $ Map.toList xs

instance PP m a => PP m (Set a) where
    pp xs = do
        pp1 <- mapM pp $ Set.toList xs
        return $ sepBy space pp1

instance (Vars iden m a,Vars iden m b) => Vars iden m (Map a b) where
    traverseVars f xs = traverseMap f f xs

traverseMap :: (GenVar iden m,IsScVar m a,IsScVar m b,IsScVar m iden,MonadIO m) => (a -> VarsM iden m a) -> (b -> VarsM iden m b) -> Map a b -> VarsM iden m (Map a b)
traverseMap f g xs = liftM Map.fromList $ aux $ Map.toList xs
        where
        aux [] = return []
        aux ((k,v):xs) = do
            k' <- f k
            v' <- g v
            xs' <- aux xs
            return ((k',v'):xs')

instance Vars iden m a => Vars iden m (Set a) where
    traverseVars f xs = liftM Set.fromList $ mapM f $ Set.toList xs

instance Vars iden m a => Vars iden m (Maybe a) where
    traverseVars f x = mapM f x

instance (PP m a,PP m b) => PP m (a,b) where
    pp (x,y) = do
        ppx <- pp x
        ppy <- pp y
        return $ ppx <+> ppy
    
instance (PP m a,PP m b,PP m c) => PP m (a,b,c) where
    pp (x,y,z) = do
        ppx <- pp x
        ppy <- pp y
        ppz <- pp z
        return $ ppx <+> ppy <+> ppz

instance (PP m a,PP m b,PP m c,PP m d) => PP m (a,b,c,d) where
    pp (x,y,z,w) = do
        ppx <- pp x
        ppy <- pp y
        ppz <- pp z
        ppw <- pp w
        return $ ppx <+> ppy <+> ppz <+> ppw
   
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

instance (Vars iden m a,Vars iden m b,Vars iden m c,Vars iden m d) => Vars iden m (a,b,c,d) where
    traverseVars f (x,y,z,w) = do
        x' <- f x
        y' <- f y
        z' <- f z
        w' <- f w
        return (x',y',z',w')
    
instance (PP m a,PP m b) => PP m (Either a b) where
    pp (Left x) = pp x
    pp (Right y) = pp y
    
instance (Vars iden2 m a,Vars iden2 m b) => Vars iden2 m (Either a b) where
    traverseVars f (Left x) = liftM Left $ f x
    traverseVars f (Right y) = liftM Right $ f y

instance (GenVar iden2 m,IsScVar m iden2,MonadIO m) => Vars iden2 m () where
    traverseVars f () = return ()

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,IsScVar m iden2,Vars iden2 m loc) => Vars iden2 m (ProcedureDeclaration iden loc) where
    traverseVars f (OperatorDeclaration l t o args ctx anns s) = do
        l' <- f l
        t' <- f t
        o' <- f o
        varsBlock $ do
            args' <- mapM f args
            ctx' <- f ctx
            anns' <- mapM f anns
            s' <- mapM f s
            return $ OperatorDeclaration l' t' o' args' ctx' anns' s'
    traverseVars f (ProcedureDeclaration l t n args ctx anns s) = do
        l' <- f l
        t' <- f t
        n' <- inLHS True $ f n
        varsBlock $ do
            args' <- mapM f args
            ctx' <- f ctx
            anns' <- mapM f anns
            s' <- mapM f s
            return $ ProcedureDeclaration l' t' n' args' ctx' anns' s'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,IsScVar m iden2,Vars iden2 m loc) => Vars iden2 m (FunctionDeclaration iden loc) where
    traverseVars f (OperatorFunDeclaration isLeak l t o args ctx anns e) = do
        isLeak' <- f isLeak
        l' <- f l
        t' <- f t
        o' <- f o
        varsBlock $ do
            args' <- mapM f args
            ctx' <- f ctx
            anns' <- mapM f anns
            e' <- f e
            return $ OperatorFunDeclaration isLeak' l' t' o' args' ctx' anns' e'
    traverseVars f (FunDeclaration isLeak l t n args ctx anns e) = do
        isLeak' <- f isLeak
        l' <- f l
        t' <- f t
        n' <- inLHS True $ f n
        varsBlock $ do
            args' <- mapM f args
            ctx' <- f ctx
            anns' <- mapM f anns
            e' <- f e
            return $ FunDeclaration isLeak' l' t' n' args' ctx' anns' e'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,IsScVar m iden2,Vars iden2 m loc) => Vars iden2 m (AxiomDeclaration iden loc) where
    traverseVars f (AxiomDeclaration isLeak l qs args anns) = do
        l' <- f l
        qs' <- inLHS False $ mapM f qs
        varsBlock $ do
            args' <- mapM f args
            anns' <- mapM f anns
            return $ AxiomDeclaration isLeak l' qs' args' anns'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,IsScVar m iden2,Vars iden2 m loc) => Vars iden2 m (LemmaDeclaration iden loc) where
    traverseVars f (LemmaDeclaration isLeak n l qs ctx args bctx anns body) = do
        isLeak' <- f isLeak
        n' <- f n
        l' <- f l
        qs' <- inLHS False $ mapM (mapM f) qs
        ctx' <- f ctx
        varsBlock $ do
            args' <- mapM f args
            bctx' <- f bctx
            anns' <- mapM f anns
            body' <- mapM f body
            return $ LemmaDeclaration isLeak' n' l' qs' ctx' args' bctx' anns' body'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,IsScVar m iden2,Vars iden2 m loc) => Vars iden2 m (ProcedureParameter iden loc) where
    traverseVars f (ProcedureParameter l isConst t isVariadic v) = do
        l' <- f l
        isConst' <- f isConst
        t' <- f t
        v' <- inLHS False $ f v
        return $ ProcedureParameter l' isConst' t' isVariadic v'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (ReturnTypeSpecifier iden loc) where
    traverseVars f (ReturnType l mb) = do
        l' <- f l
        mb' <- mapM f mb
        return $ ReturnType l' mb'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (VarName iden loc) where
    traverseVars f v@(VarName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ VarName l' n'
    substL (VarName _ n) = substL n
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (ProcedureName iden loc) where
    traverseVars f v@(ProcedureName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ ProcedureName l' n'
    substL (ProcedureName _ n) = substL n

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (DomainName iden loc) where
    traverseVars f v@(DomainName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ DomainName l' n'
    substL (DomainName _ n) = substL n

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (KindName iden loc) where
    traverseVars f v@(KindName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ KindName l' n'
    substL (KindName _ n) = substL n

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (ModuleName iden loc) where
    traverseVars f v@(ModuleName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ ModuleName l' n'
    substL (ModuleName _ n) = substL n

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (TemplateArgName iden loc) where
    traverseVars f v@(TemplateArgName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ TemplateArgName l' n'
    substL (TemplateArgName _ n) = substL n

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (AttributeName iden loc) where
    traverseVars f v@(AttributeName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ AttributeName l' n'
    substL (AttributeName _ n) = substL n

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (TypeName iden loc) where
    traverseVars f v@(TypeName l n) = do
        l' <- inRHS $ f l
        n' <- f n
        return $ TypeName l' n'
    substL (TypeName _ n) = substL n

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (TypeSpecifier iden loc) where
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

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [Statement iden loc] where
    traverseVars f xs = mapM f xs

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (Statement iden loc) where
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
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,IsScVar m iden2,Vars iden2 m loc) => Vars iden2 m (Op iden loc) where
    traverseVars f (OpCast l t) = do
        l' <- f l
        t' <- f t
        return $ OpCast l' t'
    traverseVars f o = do
        l' <- f (loc o)
        return $ updLoc o l'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (DimtypeSpecifier iden loc) where
    traverseVars f (DimSpecifier l e) = do
        l' <- f l
        e' <- f e
        return $ DimSpecifier l' e'

instance (Location loc,Vars iden2 m loc) => Vars iden2 m (BinaryAssignOp loc) where
    traverseVars f o = do
        l' <- f (loc o)
        return $ updLoc o l'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [Expression iden loc] where
    traverseVars f = mapM f

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [(Expression iden loc,IsVariadic)] where
    traverseVars f = mapM (mapFstM f)

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (Expression iden loc) where
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
    traverseVars f (BuiltinExpr l n e) = do
        l' <- f l
        n <- f n
        e' <- f e
        return $ BuiltinExpr l' n e'
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
    traverseVars f (MultisetConstructorPExpr l es) = do
        l' <- f l
        es' <- mapM f es
        return $ MultisetConstructorPExpr l' es'
    traverseVars f (SetConstructorPExpr l es) = do
        l' <- f l
        es' <- mapM f es
        return $ SetConstructorPExpr l' es'
    traverseVars f (ToMultisetExpr l e) = do
        l' <- f l
        e' <- f e
        return $ ToMultisetExpr l' e'
    traverseVars f (ToSetExpr l e) = do
        l' <- f l
        e' <- f e
        return $ ToSetExpr l' e'
    traverseVars f (SetComprehensionExpr l t x p g) = do
        l' <- f l
        varsBlock $ do
            (t',x') <- inLHS False $ f (t,x)
            p' <- f p
            g' <- f g
            return $ SetComprehensionExpr l' t' x' p' g'
    traverseVars f (ToVArrayExpr l e i) = do
        l' <- f l
        e' <- f e
        i' <- f i
        return $ ToVArrayExpr l' e' i'
    traverseVars f (RVariablePExpr l v) = do
        l' <- inRHS $ f l
        v' <- f v
        return $ RVariablePExpr l' v'
    traverseVars f (LitPExpr l lit) = do
        l' <- f l
        lit' <- f lit
        return $ LitPExpr l' lit'
    traverseVars f (ResultExpr l) = do
        l' <- f l
        return $ ResultExpr l'
    traverseVars f (QuantifiedExpr l q vs e) = do
        l' <- f l
        q' <- f q
        varsBlock $ do
            vs' <- inLHS False $ mapM f vs
            e' <- f e
            return $ QuantifiedExpr l' q' vs' e'
    
    substL (RVariablePExpr _ v) = substL $ varNameId v
    substL (ResultExpr _) = do
        v::iden <- mkVar "\\result"
        substL v
    substL e = return Nothing

instance (Location loc,DebugM m,Location loc,Vars iden2 m loc) => Vars iden2 m (Quantifier loc) where
    traverseVars f q = do
        l' <- f (loc q)
        return $ updLoc q l'

instance (Location loc,DebugM m,Location loc,Vars iden2 m loc) => Vars iden2 m (Literal loc) where
    traverseVars f lit = do
        l' <- f (loc lit)
        return $ updLoc lit l'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (Index iden loc) where
    traverseVars f (IndexSlice l e1 e2) = do
        l' <- f l
        e1' <- mapM f e1
        e2' <- mapM f e2
        return $ IndexSlice l' e1' e2'
    traverseVars f (IndexInt l e) = do
        l' <- f l
        e' <- f e
        return $ IndexInt l' e'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (CastType iden loc) where
    traverseVars f (CastPrim p) = do
        p' <- f p
        return $ CastPrim p'
    traverseVars f (CastTy t) = do
        t' <- f t
        return $ CastTy t'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (DatatypeSpecifier iden loc) where
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
    traverseVars f (MultisetSpecifier l t) = do
        l' <- f l
        t' <- f t
        return $ MultisetSpecifier l' t'
    traverseVars f (SetSpecifier l t) = do
        l' <- f l
        t' <- f t
        return $ SetSpecifier l' t'
    substL (VariableSpecifier l (TypeName _ n)) = substL n
    substL s = return Nothing
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (TemplateTypeArgument iden loc) where
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
        i' <- f i
        return $ ExprTemplateTypeArgument l' i'
    traverseVars f (PublicTemplateTypeArgument l) = do
        l' <- f l
        return $ PublicTemplateTypeArgument l'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (SecTypeSpecifier iden loc) where
    traverseVars f (PublicSpecifier l) = do
        l' <- f l
        return $ PublicSpecifier l'
    traverseVars f (PrivateSpecifier l d) = do
        l' <- f l
        d' <- f d
        return $ PrivateSpecifier l' d'
    substL (PrivateSpecifier l (DomainName _ n)) = substL n
    substL s = return Nothing

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (VariableDeclaration iden loc) where
    traverseVars f (VariableDeclaration l isConst isHavoc t is) = do
        l' <- f l
        isConst' <- f isConst
        isHavoc' <- f isHavoc
        t' <- f t
        is' <- mapM f is
        return $ VariableDeclaration l' isConst' isHavoc' t' is'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (VariableInitialization iden loc) where
    traverseVars f (VariableInitialization l v sz e) = do
        l' <- f l
        v' <- inLHS False $ f v
        sz' <- mapM f sz
        e' <- mapM f e
        return $ VariableInitialization l' v' sz' e'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (Sizes iden loc) where
    traverseVars f (Sizes es) = do
        es' <- mapM f es
        return $ Sizes es'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (SyscallParameter iden loc) where
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

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (ForInitializer iden loc) where
    traverseVars f (InitializerExpression e) = do
        e' <- mapM f e
        return $ InitializerExpression e'
    traverseVars f (InitializerVariable vd) = do
        vd' <- f vd
        return $ InitializerVariable vd'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (Module iden loc) where
    traverseVars f (Module l n p) = do
        l' <- f l
        n' <- mapM f n
        p' <- f p
        return $ Module l' n' p'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (Program iden loc) where
    traverseVars f (Program l is gs) = do
        l' <- f l
        is' <- mapM f is
        gs' <- mapM f gs
        return $ Program l' is' gs'
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (GlobalDeclaration iden loc) where
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
    traverseVars f (GlobalFunction l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalFunction l' p'
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

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (TemplateContext iden loc) where
    traverseVars f (TemplateContext l xs) = do
        l' <- f l
        xs' <- mapM (mapM f) xs
        return $ TemplateContext l' xs'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (CtxPArg iden loc) where
    traverseVars f (CtxExprPArg l isConst e isVariadic) = do
        l' <- f l
        isConst' <- f isConst
        e' <- f e
        isVariadic' <- f isVariadic
        return $ CtxExprPArg l' isConst' e' isVariadic'
    traverseVars f (CtxTypePArg l isConst t b) = do
        l' <- f l
        isConst' <- f isConst
        t' <- f t
        b' <- f b
        return $ CtxTypePArg l' isConst' t' b'
    traverseVars f (CtxVarPArg l isConst t b) = do
        l' <- f l
        isConst' <- f isConst
        t' <- f t
        b' <- f b
        return $ CtxVarPArg l' isConst' t' b'

instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m ExprClass where
    traverseVars f = return
instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m CstrKind where
    traverseVars f = return

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (ContextConstraint iden loc) where
    traverseVars f kc@(ContextPDec l cl isLeak isAnn k r n ts ps) = do
        l' <- f l
        cl' <- f cl
        isLeak' <- f isLeak
        isAnn' <- f isAnn
        k' <- f k
        r' <- f r
        n' <- f n
        ts' <- mapM (mapM f) ts
        ps' <- mapM f ps
        return $ ContextPDec l' cl' isLeak' isAnn' k' r' n' ts' ps'
    traverseVars f (ContextODec l cl isLeak isAnn k r n ts ps) = do
        l' <- f l
        cl' <- f cl
        isLeak' <- f isLeak
        isAnn' <- f isAnn
        k' <- f k
        r' <- f r
        n' <- f n
        ts' <- mapM (mapM f) ts
        ps' <- mapM f ps
        return $ ContextODec l' cl' isLeak' isAnn' k' r' n' ts' ps'
    traverseVars f (ContextTDec l cl n ts) = do
        l' <- f l
        cl' <- f cl
        n' <- f n
        ts' <- mapM f ts
        return $ ContextTDec l' cl' n' ts'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (TemplateDeclaration iden loc) where
    traverseVars f (TemplateStructureDeclaration l qs s) = do
        l' <- f l
        qs' <- mapM f qs
        s' <- f s
        return $ TemplateStructureDeclaration l' qs' s'
    traverseVars f (TemplateStructureSpecialization l qs specs s) = do
        l' <- f l
        qs' <- mapM f qs
        specs' <- mapM f specs
        s' <- f s
        return $ TemplateStructureSpecialization l' qs' specs' s'
    traverseVars f (TemplateProcedureDeclaration l qs p) = do
        l' <- f l
        qs' <- inLHS False $ mapM f qs
        p' <- f p
        return $ TemplateProcedureDeclaration l' qs' p'
    traverseVars f (TemplateFunctionDeclaration l qs p) = do
        l' <- f l
        qs' <- inLHS False $ mapM f qs
        p' <- f p
        return $ TemplateFunctionDeclaration l' qs' p'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (StructureDeclaration iden loc) where
    traverseVars f (StructureDeclaration l n ctx as) = do
        l' <- f l
        n' <- inLHS True $ f n
        ctx' <- f ctx
        as' <- mapM f as
        return $ StructureDeclaration l' n' ctx' as'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (Attribute iden loc) where
    traverseVars f (Attribute l t a szs) = do
        l' <- inRHS $ f l
        t' <- inRHS $ f t
        a' <- inLHS True $ f a
        szs' <- inRHS $ f szs
        return $ Attribute l' t' a' szs'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [AttributeName iden loc] where
    traverseVars f = mapM f

instance PP m iden => PP m [AttributeName iden loc] where
    pp atts = liftM vcat $ mapM pp atts

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [Attribute iden loc] where
    traverseVars f = mapM f

instance (Location loc,DebugM m,PP m loc,PP m iden) => PP m [Attribute iden loc] where
    pp atts = liftM vcat $ mapM pp atts

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (TemplateQuantifier iden loc) where
    traverseVars f (DomainQuantifier l b d k) = do
        l' <- f l
        b' <- f b
        d' <- inLHS False $ f d
        k' <- mapM f k
        return $ DomainQuantifier l' b' d' k'
    traverseVars f (KindQuantifier l b0 b k) = do
        l' <- f l
        b0' <- f b0
        b' <- f b
        k' <- inLHS False $ f k
        return $ KindQuantifier l' b0' b' k'
    traverseVars f (DimensionQuantifier l b d e) = do
        l' <- f l
        b' <- f b
        d' <- inLHS False $ f d
        e' <- f e
        return $ DimensionQuantifier l' b' d' e'
    traverseVars f (DataQuantifier l c b t) = do
        l' <- f l
        c' <- f c
        b' <- f b
        t' <- inLHS False $ f t
        return $ DataQuantifier l' c' b' t'

instance Monad m => PP m KindClass where
    pp = return . ppKindClass
instance Monad m => PP m DataClass where
    pp = return . ppDataClass
instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m KindClass where
    traverseVars f x = return x
instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m DataClass where
    traverseVars f x = return x

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (KindDeclaration iden loc) where
    traverseVars f (Kind l n) = do
        l' <- f l
        n' <- inLHS True $ f n
        return $ Kind l' n'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (DomainDeclaration iden loc) where
    traverseVars f (Domain l d k) = do
        l' <- f l
        d' <- inLHS True $ f d
        k' <- f k
        return $ Domain l' d' k'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [ImportDeclaration iden loc] where
    traverseVars f xs = mapM f xs

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [GlobalDeclaration iden loc] where
    traverseVars f xs = mapM f xs

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (ImportDeclaration iden loc) where
    traverseVars f (Import l m) = do
        l' <- f l
        m' <- f m
        return $ Import l' m'

instance (GenVar iden2 m,IsScVar m iden2,MonadIO m) => Vars iden2 m Position where
    traverseVars f p = return p

instance (GenVar iden2 m,IsScVar m iden2,MonadIO m) => Vars iden2 m Bool where
    traverseVars f b = return b

instance (GenVar iden2 m,IsScVar m iden2,MonadIO m) => Vars iden2 m Ordering where
    traverseVars f x = return x

instance (GenVar iden2 m,IsScVar m iden2,MonadIO m) => Vars iden2 m SecrecError where
    traverseVars f x = return x
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (LoopAnnotation iden loc) where
    traverseVars f (DecreasesAnn l isFree e) = do
        l' <- f l
        isFree' <- f isFree
        e' <- f e
        return $ DecreasesAnn l' isFree' e'
    traverseVars f (InvariantAnn l isFree isLeak e) = do
        l' <- f l
        isFree' <- f isFree
        isLeak' <- f isLeak
        e' <- f e
        return $ InvariantAnn l' isFree' isLeak' e'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (StatementAnnotation iden loc) where
    traverseVars f (AssertAnn l isLeak e) = do
        l' <- f l
        isLeak' <- f isLeak
        e' <- f e
        return $ AssertAnn l' isLeak' e'
    traverseVars f (AssumeAnn l isLeak e) = do
        l' <- f l
        isLeak' <- f isLeak
        e' <- f e
        return $ AssumeAnn l' isLeak' e'
    traverseVars f (EmbedAnn l isLeak e) = do
        l' <- f l
        isLeak' <- f isLeak
        e' <- f e
        return $ EmbedAnn l' isLeak' e'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (ProcedureAnnotation iden loc) where
    traverseVars f (RequiresAnn l isFree isLeak e) = do
        l' <- f l
        isFree' <- f isFree
        isLeak' <- f isLeak
        e' <- f e
        return $ RequiresAnn l' isFree' isLeak' e'
    traverseVars f (EnsuresAnn l isFree isLeak e) = do
        l' <- f l
        isFree' <- f isFree
        isLeak' <- f isLeak
        e' <- f e
        return $ EnsuresAnn l' isFree' isLeak' e'
    traverseVars f (PDecreasesAnn l e) = do
        l' <- f l
        e' <- f e
        return $ PDecreasesAnn l' e'
    traverseVars f (InlineAnn l b) = do
        l' <- f l
        b' <- f b
        return $ InlineAnn l' b'

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [StatementAnnotation iden loc] where
    traverseVars f xs = mapM f xs
    
instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m [ProcedureAnnotation iden loc] where
    traverseVars f xs = mapM f xs

instance (Location loc,DebugM m,GenVar iden m,Vars iden2 m iden,Location loc,Vars iden2 m loc,IsScVar m iden2) => Vars iden2 m (GlobalAnnotation iden loc) where
    traverseVars f (GlobalFunctionAnn l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalFunctionAnn l' p'
    traverseVars f (GlobalProcedureAnn l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalProcedureAnn l' p'
    traverseVars f (GlobalStructureAnn l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalStructureAnn l' p'
    traverseVars f (GlobalTemplateAnn l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalTemplateAnn l' p'
    traverseVars f (GlobalAxiomAnn l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalAxiomAnn l' p'
    traverseVars f (GlobalLemmaAnn l p) = do
        l' <- f l
        p' <- f p
        return $ GlobalLemmaAnn l' p'







    

