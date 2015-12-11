{-# LANGUAGE GADTs, StandaloneDeriving, TupleSections, DeriveDataTypeable, DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

module Language.SecreC.Utils where
    
import Language.SecreC.Pretty

import Data.Generics hiding (GT)
import Data.Traversable as Traversable
import Data.Foldable
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Maybe
import Data.Unique
import Data.IORef

import Text.PrettyPrint

import Control.Monad

import Unsafe.Coerce

mconcatNe :: Monoid a => NeList a -> a
mconcatNe = mconcat . toList

mapSetM :: (Monad m,Ord a) => (a -> m a) -> Set a -> m (Set a)
mapSetM f xs = liftM Set.fromList $ mapM f $ Set.toList xs

-- | Non-empty list
data NeList a = WrapNe a | ConsNe a (NeList a)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Foldable,Traversable)

-- | Non-empty list with separators
data SepList sep a = WrapSep a | ConsSep a sep (SepList sep a)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Foldable,Traversable)

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

foldr1M :: (Monad m,Foldable t) => (a -> a -> m a) -> t a -> m a
foldr1M f xs = liftM (fromMaybe (error "foldr1: empty structure"))
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

snocNe :: NeList a -> a -> NeList a
snocNe (WrapNe x) y = ConsNe x (WrapNe y)
snocNe (ConsNe x xs) y = ConsNe x (snocNe xs y)

lengthNe :: NeList a -> Int
lengthNe (WrapNe x) = 1
lengthNe (ConsNe x xs) = succ (lengthNe xs)

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

spanM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
spanM p [] = return ([],[])
spanM p (x:xs) = do
    ok <- p x
    if ok then do { (l,r) <- spanM p xs; return (x:l,r) } else return ([],x:xs)

mapFstM :: (Traversable t,Monad m) => (a -> m b) -> t (a,c) -> m (t (b,c))
mapFstM f = Traversable.mapM (\(a,c) -> liftM (,c) $ f a)

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
    (EqDyn a) == (EqDyn b) = (typeOf a == typeOf b) && (a == unsafeCoerce b)

toEqDyn :: (Data a,Typeable a,Eq a) => a -> EqDyn
toEqDyn v = EqDyn v

fromEqDyn :: (Data a,Typeable a,Eq a) => EqDyn -> Maybe a
fromEqDyn (EqDyn v) = case unsafeCoerce v of 
    r | typeOf v == typeOf r -> Just r
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
    (OrdDyn a) == (OrdDyn b) = (typeOf a == typeOf b) && (a == unsafeCoerce b)

instance Ord OrdDyn where
    compare (OrdDyn a) (OrdDyn b) = case compare (typeOf a) (typeOf b) of
        EQ -> compare a (unsafeCoerce b)
        c -> c

toOrdDyn :: (Data a,Typeable a,Eq a,Ord a) => a -> OrdDyn
toOrdDyn v = OrdDyn v

fromOrdDyn :: (Data a,Typeable a,Eq a,Ord a) => OrdDyn -> Maybe a
fromOrdDyn (OrdDyn v) = case unsafeCoerce v of 
    r | typeOf v == typeOf r -> Just r
      | otherwise     -> Nothing
      
data ShowOrdDyn where
    ShowOrdDyn :: (Data a,Typeable a,Eq a,Ord a,Show a) => a -> ShowOrdDyn
  deriving Typeable
  
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
    (ShowOrdDyn a) == (ShowOrdDyn b) = (typeOf a == typeOf b) && (a == unsafeCoerce b)

instance Ord ShowOrdDyn where
    compare (ShowOrdDyn a) (ShowOrdDyn b) = case compare (typeOf a) (typeOf b) of
        EQ -> compare a (unsafeCoerce b)
        c -> c

toShowOrdDyn :: (Data a,Typeable a,Eq a,Ord a,Show a) => a -> ShowOrdDyn
toShowOrdDyn v = ShowOrdDyn v

fromShowOrdDyn :: (Data a,Typeable a,Eq a,Ord a,Show a) => ShowOrdDyn -> Maybe a
fromShowOrdDyn (ShowOrdDyn v) = case unsafeCoerce v of 
    r | typeOf v == typeOf r -> Just r
      | otherwise     -> Nothing

data PPDyn where
    PPDyn :: (Data a,Typeable a,Show a,PP a) => a -> PPDyn
  deriving Typeable
  
instance Data PPDyn where
    gfoldl k z (PPDyn x) = z PPDyn `k` x
    gunfold = error "gunfold unsupported"
    toConstr (PPDyn _) = conPPDyn
    dataTypeOf _ = tyPPDyn

conPPDyn = mkConstr tyPPDyn "PPDyn" [] Prefix
tyPPDyn = mkDataType "Language.SecreC.Utils.PPDyn" [conPPDyn]
  
instance Show PPDyn where
    show (PPDyn d) = show d

instance PP PPDyn where
    pp (PPDyn d) = pp d

instance Show (IORef a) where
    show _ = "<IORef>"

toPPDyn :: (Data a,Typeable a,Show a,PP a) => a -> PPDyn
toPPDyn v = PPDyn v

fromPPDyn :: (Data a,Typeable a,Show a,PP a) => PPDyn -> Maybe a
fromPPDyn (PPDyn v) = case unsafeCoerce v of 
    r | typeOf v == typeOf r -> Just r
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

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

typeOfProxy :: Typeable a => Proxy a -> TypeOf a
typeOfProxy p = TypeOf (typeOf p)

eqTypeOf :: TypeOf a -> TypeOf b -> EqT a b
eqTypeOf (TypeOf t1) (TypeOf t2) = if t1 == t2 then unsafeCoerce EqT else NeqT

instance Show (a -> b) where
    show _ = "<function>"

instance Show Unique where
    show = show . hashUnique

data UniqRef a = UniqRef
    { uniqId :: Unique
    , uniqRef :: !(IORef a)
    }
  deriving (Data,Typeable)

instance Eq (UniqRef a) where
    i1 == i2 = uniqId i1 == uniqId i2
instance Ord (UniqRef a) where
    compare i1 i2 = compare (uniqId i1) (uniqId i2)
    
instance Show (UniqRef a) where
    show r = "<UniqRef>"
    
instance PP (UniqRef a) where
    pp r = text (show r)
    
newUniqRef :: a -> IO (UniqRef a)
newUniqRef a = do
    i <- newUnique
    r <- newIORef a
    return $ UniqRef i r

readUniqRef :: UniqRef a -> IO a
readUniqRef r = readIORef (uniqRef r)

writeUniqRef :: UniqRef a -> a -> IO ()
writeUniqRef r x = writeIORef (uniqRef r) x

instance Data Unique where
    gunfold = error "gunfold Unique"
    toConstr = error "toConstr Unique"
    dataTypeOf = error "dataTypeof Unique"