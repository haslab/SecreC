{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, RankNTypes, GADTs, StandaloneDeriving, TupleSections, DeriveDataTypeable, DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

module Language.SecreC.Utils where
    
import Language.SecreC.Pretty

import Data.Binary
import Data.Binary.Get as Binary
import Data.Generics as Generics hiding (GT,typeOf,Generic,empty)
import qualified Data.Generics as Generics
import GHC.Generics (Generic)
import Data.Traversable as Traversable
import Data.Foldable as Foldable
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Maybe
import Data.Unique
import Data.IORef
import Data.Hashable
import Data.Graph.Inductive.PatriciaTree as Graph
import Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.Monad as Graph
import Data.Graph.Inductive.Query.DFS as Graph
import Data.Graph.Inductive.Basic as Graph
import Data.Char
import Data.List as List
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Internal as BL
import qualified Data.ByteString as BS

import Text.PrettyPrint

import qualified GHC.Generics as G

import Control.Monad
import Control.Concurrent.Async
import Control.Concurrent
import Control.Monad.Trans
import Control.Monad.Except

import Unsafe.Coerce

import System.Mem.Weak.Exts as Weak
import System.Directory
import System.IO.Error
import System.IO
import System.Process

import Safe

insNewNodeIO :: DynGraph gr => a -> gr a b -> IO (gr a b)
insNewNodeIO x gr = do
    n <- newNodeGrIO gr
    return $ insNode (n,x) gr

newNodeGrIO :: DynGraph gr => gr a b -> IO Int
newNodeGrIO gr = aux
    where
    is = nodes gr
    aux = do
        i <- liftM hashUnique newUnique
        if (elem i is) then aux else return i

tryInsEdge :: DynGraph gr => LEdge b -> gr a b -> gr a b
tryInsEdge e@(from,to,b) gr = if gelem from gr && gelem to gr then insEdge e gr else gr

tryInsEdges :: DynGraph gr => [LEdge b] -> gr a b -> gr a b
tryInsEdges [] gr = gr
tryInsEdges (x:xs) gr = tryInsEdges xs (tryInsEdge x gr)

insLabEdges :: DynGraph gr => [(LNode a,LNode a,b)] -> gr a b -> gr a b
insLabEdges [] gr = gr
insLabEdges (x:xs) gr = insLabEdges xs (insLabEdge x gr)

insLabEdge :: DynGraph gr => (LNode a,LNode a,b) -> gr a b -> gr a b
insLabEdge ((x1,x2),(y1,y2),b) gr = insEdge (x1,y1,b) $ tryInsNode (x1,x2) $ tryInsNode (y1,y2) gr

tryInsNode :: DynGraph gr => LNode a -> gr a b -> gr a b
tryInsNode (n,v) gr = if gelem n gr then gr else insNode (n,v) gr

-- find all roots in a directed graph
rootsGr :: DynGraph gr => gr a b -> [LNode a]
rootsGr gr = labNodes $ subgraph ins gr
    where
    ins = nodes gr \\ (map snd $ filter (\(x,y) -> x /= y) $ edges gr)

-- find all terminals in a directed graph
endsGr :: DynGraph gr => gr a b -> [LNode a]
endsGr gr = labNodes $ subgraph ins gr
    where
    ins = nodes gr \\ (map fst $ filter (\(x,y) -> x /= y) $ edges gr)

elimSpaces :: String -> String
elimSpaces = filter (not . isSpace)

contextGr :: (Graph gr) => gr a b -> Node -> Maybe (Context a b)
contextGr g v = fst (Graph.match v g)

reachablesGr :: (Graph gr) => [Node] -> gr a b -> [Node]
reachablesGr vs g = preorderF (dff vs g)

mapGrM :: (Monad m,DynGraph gr) => (Context a b -> m (Context c d)) -> gr a b -> m (gr c d)
mapGrM f gr = ufold g (return Graph.empty) gr
    where
    g ctx m = do
        ctx' <- f ctx
        liftM (ctx' &) m

nmapM :: (Monad m,DynGraph gr) => (a -> m c) -> gr a b -> m (gr c b)
nmapM f gr = mapGrM aux gr
    where
    aux (froms,n,x,tos) = do
        x' <- f x
        return (froms,n,x',tos)

labnfilterM :: (Monad m,DynGraph gr) => (LNode a -> m Bool) -> gr a b -> m (gr a b)
labnfilterM p gr = ufold aux (return Graph.empty) gr
    where
    aux ctx@(_,n,i,_) m = do
        ok <- p (n,i)
        if ok then liftM (ctx &) m else m

grToList :: Gr a b -> [Context a b]
grToList = ufold (:) []

unionGr :: Gr a b -> Gr a b -> Gr a b
unionGr x y = insEdges (labEdges x ++ labEdges y) $ insNodes (labNodes x ++ labNodes y) Graph.empty

differenceGr :: Gr a b -> Gr a b -> Gr a b
differenceGr x y = Graph.nfilter (\x -> not $ elem x ys) x
    where ys = nodes y

ppGrM :: Monad m => (a -> m Doc) -> (b -> m Doc) -> Gr a b -> m Doc
ppGrM ppA ppB gr = liftM vcat $ mapM ppNode $ grToList gr
    where
    ppNode (froms,k,v,tos) = do
        vDoc <- ppA v
        tosDoc <- liftM (sepBy comma) $ do
            xs <- mapM ppFrom froms
            ys <- mapM ppTo tos
            return (xs++ys)
        return $ vDoc $+$ nest 4 tosDoc
    ppTo (tolbl,toid) = do
        tolblDoc <- ppB tolbl
        toDoc <- pp toid
        return $ text "-" <> tolblDoc <> text "->" <+> toDoc
    ppFrom (fromlbl,fromid) = do
        fromlblDoc <- ppB fromlbl
        fromDoc <- pp fromid
        return $ fromDoc <+> text "-" <> fromlblDoc <> text "->"

instance (PP m a,PP m b) => PP m (Gr a b) where
    pp = ppGrM pp pp
        
instance (Ord a,Ord b) => Ord (Gr a b) where
    compare x y = compare (OrdGr x) (OrdGr y)
    
deriving instance Typeable (Gr a b)

deriving instance (Typeable i,Data c,Typeable p) => Data (G.K1 i c p)
deriving instance (Typeable i,Typeable c,Typeable p,Typeable f,Data (f p)) => Data (G.M1 i c f p)

instance (Binary a,Binary b) => Binary (Gr a b)

fromX :: G.Generic x => x -> G.Rep x x
fromX = G.from
toX :: G.Generic x => G.Rep x x -> x
toX = G.to

instance (Data a,Data b) => Data (Gr a b) where
    gfoldl k z gr = z toX `k` (fromX gr)

mapFoldlM :: Monad m => (a -> k -> v -> m a) -> a -> Map k v -> m a
mapFoldlM f z m = foldlM (\x (y,z) -> f x y z) z $ Map.toList m

instance WeakKey (IdRef id a) where
    mkWeakKey r = mkWeakKey (idRef r)

mconcatNe :: Monoid a => NeList a -> a
mconcatNe = mconcat . toList

mapSet :: (Ord a,Ord b) => (a -> b) -> Set a -> Set b
mapSet f xs = Set.fromList $ map f $ Set.toList xs

mapSetM :: (Monad m,Ord a,Ord b) => (a -> m b) -> Set a -> m (Set b)
mapSetM f xs = liftM Set.fromList $ mapM f $ Set.toList xs

filterSetM :: (Monad m,Ord a) => (a -> m Bool) -> Set a -> m (Set a)
filterSetM f xs = liftM Set.fromList $ filterM f $ Set.toList xs

orM :: Monad m => m Bool -> m Bool -> m Bool
orM mx my = do
    x <- mx
    y <- my
    return (x || y)

-- | Non-empty list
data NeList a = WrapNe a | ConsNe a (NeList a)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Foldable,Traversable,Generic)
instance Binary a => Binary (NeList a)

-- | Non-empty list with separators
data SepList sep a = WrapSep a | ConsSep a sep (SepList sep a)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Foldable,Traversable,Generic)
instance (Binary sep,Binary a) => Binary (SepList sep a)

foldNeM :: Monad m => (a -> b -> m b) -> (a -> m b) -> NeList a -> m b
foldNeM f g (WrapNe x) = g x
foldNeM f g (ConsNe x xs) = do
    y <- foldNeM f g xs
    f x y
    
foldSepM :: Monad m => (a -> sep -> b -> m b) -> (a -> m b) -> SepList sep a -> m b
foldSepM f g (WrapSep x) = g x
foldSepM f g (ConsSep x sep xs) = do
    y <- foldSepM f g xs
    f x sep y

foldr0M :: (Monad m) => a -> (a -> a -> m a) -> [a] -> m a
foldr0M x f [] = return x
foldr0M x f xs = foldr1M f xs

foldr0M_ :: (Monad m) => (a -> a -> m a) -> [a] -> m ()
foldr0M_ f [] = return ()
foldr0M_ f xs = foldr1M_ f xs

foldr1M_ :: (Monad m,Foldable t) => (a -> a -> m a) -> t a -> m ()
foldr1M_ f xs = foldr1M f xs >> return ()

foldr1M :: (Monad m,Foldable t) => (a -> a -> m a) -> t a -> m a
foldr1M f xs = liftM (fromMaybe (error "foldr1M: empty structure"))
                    (foldrM mf Nothing xs)
      where
        mf x m = liftM Just (case m of
                         Nothing -> return x
                         Just y  -> f x y)

fromListNe :: [a] -> NeList a
fromListNe [x] = WrapNe x
fromListNe (x:xs) = ConsNe x $ fromListNe xs

snocSep :: SepList sep a -> sep -> a -> SepList sep a
snocSep (WrapSep x) sep y = ConsSep x sep (WrapSep y)
snocSep (ConsSep x s xs) sep y = ConsSep x s (snocSep xs sep y)

headSep :: SepList sep a -> a
headSep (WrapSep x) = x
headSep (ConsSep x _ _) = x

updHeadSep :: (a -> a) -> SepList sep a -> SepList sep a
updHeadSep f (WrapSep x) = WrapSep (f x)
updHeadSep f (ConsSep x s xs) = ConsSep (f x) s xs

headNe :: NeList a -> a
headNe (WrapNe x) = x
headNe (ConsNe x _) = x

updHeadNe :: (a -> a) -> NeList a -> NeList a
updHeadNe f (WrapNe x) = WrapNe (f x)
updHeadNe f (ConsNe x xs) = ConsNe (f x) xs

updHeadNeM :: Monad m => (a -> m (x,a)) -> NeList a -> m (x,NeList a)
updHeadNeM f (WrapNe x) = do
    (r,x') <- f x
    return (r,WrapNe x')
updHeadNeM f (ConsNe x xs) = do
    (r,x') <- f x
    return (r,ConsNe x' xs)

updHeadM :: Monad m => (a -> m (x,a)) -> [a] -> m (x,[a])
updHeadM f (x:xs) = do
    (r,x') <- f x
    return (r,x':xs)

mapHead :: (a -> a) -> [a] -> [a]
mapHead f [] = []
mapHead f (x:xs) = (f x:xs)

snocNe :: NeList a -> a -> NeList a
snocNe (WrapNe x) y = ConsNe x (WrapNe y)
snocNe (ConsNe x xs) y = ConsNe x (snocNe xs y)

lengthNe :: NeList a -> Int
lengthNe (WrapNe x) = 1
lengthNe (ConsNe x xs) = succ (lengthNe xs)

filterMapWithKeyM :: (Ord k,Monad m) => (k -> b -> m Bool) -> Map k b -> m (Map k b)
filterMapWithKeyM f xs = Map.foldlWithKey (\mc k b -> f k b >>= \ok -> if ok then liftM (Map.insert k b) mc else mc) (return Map.empty) xs

forMapWithKeyM_ :: Monad m => Map k b -> (k -> b -> m c) -> m ()
forMapWithKeyM_ xs f = Map.foldlWithKey (\mc k b -> mc >> f k b >> return ()) (return ()) xs

forSetM_ :: Monad m => Set b -> (b -> m c) -> m ()
forSetM_ xs f = Set.foldl (\mc b -> mc >> f b >> return ()) (return ()) xs

zipLeft :: [a] -> [b] -> [(a,Maybe b)]
zipLeft [] ys = []
zipLeft xs [] = map (,Nothing) xs
zipLeft (x:xs) (y:ys) = (x,Just y) : zipLeft xs ys

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f [] = return ([],[])
partitionM f (x:xs) = do
    b <- f x
    (l,r) <- partitionM f xs
    if b then return (x:l,r) else return (l,x:r)

-- | monadic @span@ from tail to head
trailingM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
trailingM p xs = do
    (l,r) <- spanM p (reverse xs)
    return (reverse r,reverse l)

spanMaybeM :: Monad m => (a -> m (Maybe c)) -> [a] -> m ([c],[a])
spanMaybeM p [] = return ([],[])
spanMaybeM p (x:xs) = do
    ok <- p x
    case ok of
        Just c -> do
            (l,r) <- spanMaybeM p xs
            return (c:l,r)
        Nothing -> return ([],x:xs)

spanM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
spanM p [] = return ([],[])
spanM p (x:xs) = do
    ok <- p x
    if ok then do { (l,r) <- spanM p xs; return (x:l,r) } else return ([],x:xs)

mapFst :: (a -> b) -> (a,c) -> (b,c)
mapFst f (x,y) = (f x,y)

mapSnd :: (c -> b) -> (a,c) -> (a,b)
mapSnd f (x,y) = (x,f y)

mapFstM :: Monad m => (a -> m b) -> (a,c) -> m (b,c)
mapFstM f (x,y) = do
    x' <- f x
    return (x',y)

mapSndM :: Monad m => (c -> m b) -> (a,c) -> m (a,b)
mapSndM f (x,y) = do
    y' <- f y
    return (x,y')

fmapFst :: (Functor t) => (a -> b) -> t (a,c) -> t (b,c)
fmapFst f = fmap (\(a,c) -> (,c) $ f a)

fmapSnd :: (Functor t) => (b -> c) -> t (a,b) -> t (a,c)
fmapSnd f = fmap (\(a,c) -> (a,) $ f c)

fmapFstM :: (Traversable t,Monad m) => (a -> m b) -> t (a,c) -> m (t (b,c))
fmapFstM f = Traversable.mapM (\(a,c) -> liftM (,c) $ f a)

fmapSndM :: (Traversable t,Monad m) => (c -> m b) -> t (a,c) -> m (t (a,b))
fmapSndM f = Traversable.mapM (\(a,c) -> liftM (a,) $ f c)

funzip :: Traversable t => t (a,b) -> (t a,t b)
funzip xs = (fmap fst xs,fmap snd xs)

mapAndUnzipM :: (Monad m,Traversable t) => (c -> m (a,b)) -> t c -> m (t a,t b)
mapAndUnzipM f = liftM funzip . Traversable.mapM f

sortByM :: Monad m => (a -> a -> m Ordering) -> [a] -> m [a]
sortByM cmp = mergeAll <=< sequences
  where
    sequences (a:b:xs) = do { ok <- a `cmp` b; if ok == GT then descending b [a]  xs else ascending  b (a:) xs }
    sequences xs = return [xs]

    descending a as (b:bs) = do { ok <- a `cmp` b; if ok == GT then descending b (a:as) bs else liftM ((a:as):) (sequences (b:bs)) }
    descending a as bs  = liftM ((a:as):) (sequences bs)

    ascending a as (b:bs) = do { ok <- a `cmp` b; if ok /= GT then ascending b (\ys -> as (a:ys)) bs else liftM (as [a]:) (sequences (b:bs)) }
    ascending a as bs   = liftM (as [a]:) (sequences bs)

    mergeAll [x] = return x
    mergeAll xs  = mergePairs xs >>= mergeAll

    mergePairs (a:b:xs) = do { h <- merge a b;  t <- mergePairs xs; return (h:t) }
    mergePairs xs       = return xs

    merge as@(a:as') bs@(b:bs') = do { ok <- a `cmp` b; if ok == GT then liftM (b:) (merge as bs') else liftM (a:) (merge as' bs) }
    merge [] bs         = return bs
    merge as []         = return as

data EqDyn where
    EqDyn :: (Data a,Typeable a,Eq a) => a -> EqDyn
  deriving Typeable

instance Data EqDyn where
    gfoldl k z (EqDyn x) = z EqDyn `k` x
    gunfold = error "gunfold unsupported"
    toConstr (EqDyn _) = conEqDyn
    dataTypeOf _ = tyEqDyn

conEqDyn = mkConstr tyEqDyn "EqDyn" [] Prefix
tyEqDyn = mkDataType "Language.SecreC.Utils.EqDyn" [conEqDyn]

instance Show EqDyn where
    show q = "EqDyn"

instance Eq EqDyn where
    (EqDyn a) == (EqDyn b) = (Generics.typeOf a == Generics.typeOf b) && (a == unsafeCoerce b)

toEqDyn :: (Data a,Typeable a,Eq a) => a -> EqDyn
toEqDyn v = EqDyn v

fromEqDyn :: (Data a,Typeable a,Eq a) => EqDyn -> Maybe a
fromEqDyn (EqDyn v) = case unsafeCoerce v of 
    r | Generics.typeOf v == Generics.typeOf r -> Just r
      | otherwise     -> Nothing
      
data OrdDyn where
    OrdDyn :: (Data a,Typeable a,Eq a,Ord a) => a -> OrdDyn
  deriving Typeable
  
instance Data OrdDyn where
    gfoldl k z (OrdDyn x) = z OrdDyn `k` x
    gunfold = error "gunfold unsupported"
    toConstr (OrdDyn _) = conOrdDyn
    dataTypeOf _ = tyOrdDyn

conOrdDyn = mkConstr tyOrdDyn "OrdDyn" [] Prefix
tyOrdDyn = mkDataType "Language.SecreC.Utils.OrdDyn" [conOrdDyn]
  
instance Show OrdDyn where
    show d = "OrdDyn"

instance Eq OrdDyn where
    (OrdDyn a) == (OrdDyn b) = (Generics.typeOf a == Generics.typeOf b) && (a == unsafeCoerce b)

instance Ord OrdDyn where
    compare (OrdDyn a) (OrdDyn b) = case compare (Generics.typeOf a) (Generics.typeOf b) of
        EQ -> compare a (unsafeCoerce b)
        c -> c

toOrdDyn :: (Data a,Typeable a,Eq a,Ord a) => a -> OrdDyn
toOrdDyn v = OrdDyn v

fromOrdDyn :: (Data a,Typeable a,Eq a,Ord a) => OrdDyn -> Maybe a
fromOrdDyn (OrdDyn v) = case unsafeCoerce v of 
    r | Generics.typeOf v == Generics.typeOf r -> Just r
      | otherwise     -> Nothing
      
data ShowOrdDyn where
    ShowOrdDyn :: (Hashable a,Data a,Typeable a,Eq a,Ord a,Show a) => a -> ShowOrdDyn
  deriving Typeable

instance Hashable ShowOrdDyn where
    hashWithSalt i (ShowOrdDyn x) = hashWithSalt i x
  
instance Data ShowOrdDyn where
    gfoldl k z (ShowOrdDyn x) = z ShowOrdDyn `k` x
    gunfold = error "gunfold unsupported"
    toConstr (ShowOrdDyn _) = conShowOrdDyn
    dataTypeOf _ = tyShowOrdDyn

conShowOrdDyn = mkConstr tyShowOrdDyn "ShowOrdDyn" [] Prefix
tyShowOrdDyn = mkDataType "Language.SecreC.Utils.ShowOrdDyn" [conShowOrdDyn]
  
instance Show ShowOrdDyn where
    show (ShowOrdDyn d) = show d

instance Eq ShowOrdDyn where
    (ShowOrdDyn a) == (ShowOrdDyn b) = (Generics.typeOf a == Generics.typeOf b) && (a == unsafeCoerce b)

instance Ord ShowOrdDyn where
    compare (ShowOrdDyn a) (ShowOrdDyn b) = case compare (Generics.typeOf a) (Generics.typeOf b) of
        EQ -> compare a (unsafeCoerce b)
        c -> c

applyShowOrdDyn :: (forall a . (Hashable a,Data a,Typeable a,Eq a,Ord a,Show a) => a -> b) -> ShowOrdDyn -> b
applyShowOrdDyn f (ShowOrdDyn x) = f x

toShowOrdDyn :: (Hashable a,Data a,Typeable a,Eq a,Ord a,Show a) => a -> ShowOrdDyn
toShowOrdDyn v = ShowOrdDyn v

fromShowOrdDyn :: (Hashable a,Data a,Typeable a,Eq a,Ord a,Show a) => ShowOrdDyn -> Maybe a
fromShowOrdDyn (ShowOrdDyn v) = case unsafeCoerce v of 
    r | Generics.typeOf v == Generics.typeOf r -> Just r
      | otherwise     -> Nothing

data PPDyn m where
    PPDyn :: (Data a,Typeable a,Show a,PP m a) => a -> PPDyn m
  deriving Typeable
  
instance Typeable m => Data (PPDyn m) where
    gfoldl k z (PPDyn x) = z PPDyn `k` x
    gunfold = error "gunfold unsupported"
    toConstr (PPDyn _) = conPPDyn
    dataTypeOf _ = tyPPDyn

conPPDyn = mkConstr tyPPDyn "PPDyn" [] Prefix
tyPPDyn = mkDataType "Language.SecreC.Utils.PPDyn" [conPPDyn]
  
instance Show (PPDyn m) where
    show (PPDyn d) = show d

instance Monad m => PP m (PPDyn m) where
    pp (PPDyn d) = pp d

instance Show (IORef a) where
    show _ = "<IORef>"

toPPDyn :: (Data a,Typeable a,Show a,PP m a) => a -> PPDyn m
toPPDyn v = PPDyn v

fromPPDyn :: (Data a,Typeable a,Show a,PP m a) => PPDyn m -> Maybe a
fromPPDyn (PPDyn v) = case unsafeCoerce v of 
    r | Generics.typeOf v == Generics.typeOf r -> Just r
      | otherwise     -> Nothing

within :: Ord a => (a,a) -> (a,a) -> Bool
within (min1,max1) (min2,max2) = min1 >= min2 && min1 <= max2 && max1 >= min2 && max1 <= max2


-- | A monomorphic type representation to support type equality
data TypeOf a where
    TypeOf :: Typeable a => TypeRep -> TypeOf a

compareTypeOf :: TypeOf a -> TypeOf b -> Ordering
compareTypeOf (TypeOf t1) (TypeOf t2) = compare t1 t2

data EqT a b where
    EqT :: EqT a a -- evidence that two types are equal
    NeqT :: EqT a b -- evidence that two types are not equal

typeRep :: Typeable a => TypeOf a
typeRep = typeOf (error "typeRep")

typeOf :: Typeable a => a -> TypeOf a
typeOf = typeOfProxy . proxyOf

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

typeOfProxy :: Typeable a => Proxy a -> TypeOf a
typeOfProxy p = TypeOf (Generics.typeOf p)

eqTypeOf :: TypeOf a -> TypeOf b -> EqT a b
eqTypeOf (TypeOf t1) (TypeOf t2) = if t1 == t2 then unsafeCoerce EqT else NeqT

instance Show (a -> b) where
    show _ = "<function>"

instance Show Unique where
    show = show . hashUnique

data IdRef id a = IdRef
    { uniqId :: !id
    , idRef :: !(IORef a)
    }
  deriving (Data,Typeable)

instance Eq id => Eq (IdRef id a) where
    i1 == i2 = uniqId i1 == uniqId i2
instance Ord id => Ord (IdRef id a) where
    compare i1 i2 = compare (uniqId i1) (uniqId i2)
    
instance Show (IdRef id a) where
    show r = "<IdRef id>"
    
instance Monad m => PP m (IdRef id a) where
    pp r = return $ text (show r)
    
newIdRef :: id -> a -> IO (IdRef id a)
newIdRef i a = do
    r <- newIORef a
    return $ IdRef i r

readIdRef :: IdRef id a -> IO a
readIdRef r = readIORef (idRef r)

writeIdRef :: IdRef id a -> a -> IO ()
writeIdRef r x = writeIORef (idRef r) x

instance Data Unique where
    gunfold = error "gunfold Unique"
    toConstr = error "toConstr Unique"
    dataTypeOf = error "dataTypeof Unique"
    
fst3 (x,y,z) = x
snd3 (x,y,z) = y
thr3 (x,y,z) = z

fst4 (x,y,z,w) = x
snd4 (x,y,z,w) = y
thr4 (x,y,z,w) = z
fou4 (x,y,z,w) = w

instance Hashable Unique where
    hashWithSalt i a = hashWithSalt i (hashUnique a)

funit :: Functor f => f a -> f ()
funit = fmap (const ())

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

instance Hashable a => Hashable (Set a) where
    hashWithSalt i x = hashWithSalt i (Set.toList x)

instance Hashable a => Hashable (NeList a) where
    hashWithSalt i x = hashWithSalt i (Foldable.toList x)

instance (Hashable a,Hashable b) => Hashable (Map a b) where
    hashWithSalt i x = hashWithSalt i (Map.toList x)

instance (Hashable a,Hashable b) => Hashable (Gr a b) where
    hashWithSalt i x = hashWithSalt i (grToList x)

decodeFileLazy :: Binary a => FilePath -> IO a
decodeFileLazy fn = do
    input <- BL.readFile fn
    return $ Binary.runGet get input

decodeFileOrFailLazy :: Binary a => FilePath -> IO (Either (ByteOffset, String) a)
decodeFileOrFailLazy fn = do
    input <- BL.readFile fn
    case Binary.runGetOrFail get input of
        Left (_,off,err) -> return $ Left (off,err)
        Right (_,_,x) -> return $ Right x

takeHeadChunk :: BL.ByteString -> Maybe BS.ByteString
takeHeadChunk lbs =
  case lbs of
    (BL.Chunk bs _) -> Just bs
    _ -> Nothing

dropHeadChunk :: BL.ByteString -> BL.ByteString
dropHeadChunk lbs =
  case lbs of
    (BL.Chunk _ lbs') -> lbs'
    _ -> BL.Empty

tryError :: MonadError e m => m a -> m (Either e a)
tryError m = catchError (liftM Right m) (return . Left)

data Lns s v = Lns { getLns :: s -> v, putLns :: s -> v -> s }

compLns :: Lns a b -> Lns b c -> Lns a c
compLns l1 l2 = Lns get put
    where
    get = getLns l2 . getLns l1
    put a c = putLns l1 a (putLns l2 (getLns l1 a) c)
    

canonicalPath :: FilePath -> IO FilePath
canonicalPath f = catchIOError (canonicalizePath f) (const $ return f)
    
runShellCommand :: String -> IO String
runShellCommand cmd = do
    hPutStrLn stderr $ "Running command " ++ cmd
    let process = (shell cmd) { std_out = CreatePipe }
    (_,Just hout,_,ph) <- createProcess process
    result <- hGetContents hout
    waitForProcess ph
    return result

leftsMap :: (Ord a) => Map (Either a b) x -> Map a x
leftsMap = Map.foldrWithKey f Map.empty
    where
    f (Right b) v xs = xs
    f (Left a) v xs = Map.insert a v xs
    
rightsMap :: (Ord b) => Map (Either a b) x -> Map b x
rightsMap = Map.foldrWithKey f Map.empty
    where
    f (Left a) v xs = xs
    f (Right b) v xs = Map.insert b v xs

