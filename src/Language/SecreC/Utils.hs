{-# LANGUAGE TupleSections, DeriveDataTypeable, DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

module Language.SecreC.Utils where

import Data.Generics hiding (GT)
import Data.Traversable as Traversable
import Data.Foldable
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set

import Control.Monad

-- | Non-empty list
data NeList a = WrapNe a | ConsNe a (NeList a)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Foldable,Traversable)

-- | Non-empty list with separators
data SepList sep a = WrapSep a | ConsSep a sep (SepList sep a)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Foldable,Traversable)

fromListNe :: [a] -> NeList a
fromListNe [x] = WrapNe x
fromListNe (x:xs) = ConsNe x $ fromListNe xs

snocSep :: SepList sep a -> sep -> a -> SepList sep a
snocSep (WrapSep x) sep y = ConsSep x sep (WrapSep y)
snocSep (ConsSep x s xs) sep y = ConsSep x s (snocSep xs sep y)

headSep :: SepList sep a -> a
headSep (WrapSep x) = x
headSep (ConsSep x _ _) = x

headNe :: NeList a -> a
headNe (WrapNe x) = x
headNe (ConsNe x _) = x

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

