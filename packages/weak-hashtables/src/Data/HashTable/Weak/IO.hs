{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE CPP            #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExplicitForAll #-}

-- | This module provides wrappers in 'IO' around the functions from
-- "Data.HashTable.Class".
--
-- This module exports three concrete hash table types, one for each hash table
-- implementation in this package:
--
-- > type BasicHashTable  k v = IOHashTable (B.HashTable)  k v
-- > type CuckooHashTable k v = IOHashTable (Cu.HashTable) k v
-- > type LinearHashTable k v = IOHashTable (L.HashTable)  k v
--
-- The 'IOHashTable' type can be thought of as a wrapper around a concrete
-- hashtable type, which sets the 'ST' monad state type to 'PrimState' 'IO',
-- a.k.a. 'RealWorld':
--
-- > type IOHashTable tabletype k v = tabletype (PrimState IO) k v
--
-- This module provides 'stToIO' wrappers around the hashtable functions (which
-- are in 'ST') to make it convenient to use them in 'IO'. It is intended to be
-- imported qualified and used with a user-defined type alias, i.e.:
--
-- > import qualified Data.HashTable.IO as H
-- >
-- > type HashTable k v = H.CuckooHashTable k v
-- >
-- > foo :: IO (HashTable Int Int)
-- > foo = do
-- >     ht <- H.new
-- >     H.insert ht 1 1
-- >     return ht
--
-- Essentially, anywhere you see @'IOHashTable' h k v@ in the type signatures
-- below, you can plug in any of @'BasicHashTable' k v@, @'CuckooHashTable' k
-- v@, or @'LinearHashTable' k v@.
--
module Data.HashTable.Weak.IO
  ( BasicHashTable
  , CuckooHashTable
--  , LinearHashTable
  , IOHashTable
  , new
  , newSized, newSizedWithMkWeak
  , insert, insertWeak, insertWithMkWeak
  , delete
  , lookup
  , fromList
  , fromListWithSizeHint
  , toList
  , mapM_, mapWeakM_
  , foldM, foldWeakM, foldStopM
  , computeOverhead, finalize
  ) where


------------------------------------------------------------------------------
import           Control.Monad.Primitive       (PrimState)
import           Control.Monad.ST              (stToIO)
import           Data.Hashable                 (Hashable)
import qualified Data.HashTable.Weak.Class          as C
import           Prelude                       hiding (lookup, mapM_)
import qualified System.Mem.Weak.Exts as Weak
import System.Mem.Weak.Exts (MkWeak(..),Weak(..))
------------------------------------------------------------------------------
import           Data.HashTable.Weak.Internal.Utils (unsafeIOToST)
import qualified Data.HashTable.Weak.ST.Basic       as B
import qualified Data.HashTable.Weak.ST.Cuckoo      as Cu
--import qualified Data.HashTable.ST.Linear      as L


------------------------------------------------------------------------------
-- | A type alias for a basic open addressing hash table using linear
-- probing. See "Data.HashTable.ST.Basic".
type BasicHashTable k v = IOHashTable (B.HashTable) k v

-- | A type alias for the cuckoo hash table. See "Data.HashTable.ST.Cuckoo".
type CuckooHashTable k v = IOHashTable (Cu.HashTable) k v

-- | A type alias for the linear hash table. See "Data.HashTable.ST.Linear".
--type LinearHashTable k v = IOHashTable (L.HashTable) k v


------------------------------------------------------------------------------
-- | A type alias for our hash tables, which run in 'ST', to set the state
-- token type to 'PrimState' 'IO' (aka 'RealWorld') so that we can use them in
-- 'IO'.
type IOHashTable tabletype k v = tabletype (PrimState IO) k v

------------------------------------------------------------------------------
-- | See the documentation for this function in "Data.HashTable.Class#v:new".
new :: (Eq k,Hashable k,C.HashTable h) => IO (IOHashTable h k v)
new = stToIO C.new
{-# INLINE new #-}
{-# SPECIALIZE INLINE new :: (Eq k,Hashable k) => IO (BasicHashTable k v) #-}
--{-# SPECIALIZE INLINE new :: IO (LinearHashTable k v) #-}
{-# SPECIALIZE INLINE new :: (Eq k,Hashable k) => IO (CuckooHashTable k v) #-}

------------------------------------------------------------------------------
-- | See the documentation for this function in
-- "Data.HashTable.Class#v:newSized".
newSized :: (Eq k,Hashable k,C.HashTable h) => Int -> IO (IOHashTable h k v)
newSized = stToIO . C.newSized
{-# INLINE newSized #-}
{-# SPECIALIZE INLINE newSized :: (Eq k,Hashable k) => Int -> IO (BasicHashTable k v) #-}
--{-# SPECIALIZE INLINE newSized :: Int -> IO (LinearHashTable k v) #-}
{-# SPECIALIZE INLINE newSized :: (Eq k,Hashable k) => Int -> IO (CuckooHashTable k v) #-}

newSizedWithMkWeak :: (Eq k,Hashable k,C.HashTable h) => Int -> MkWeak -> IO (IOHashTable h k v)
newSizedWithMkWeak mkWeak = stToIO . C.newSizedWithMkWeak mkWeak
{-# INLINE newSizedWithMkWeak #-}
{-# SPECIALIZE INLINE newSizedWithMkWeak :: (Eq k,Hashable k) => Int -> MkWeak -> IO (BasicHashTable k v) #-}
{-# SPECIALIZE INLINE newSizedWithMkWeak :: (Eq k,Hashable k) => Int -> MkWeak -> IO (CuckooHashTable k v) #-}

------------------------------------------------------------------------------
-- | See the documentation for this function in "Data.HashTable.Class#v:insert".
insert   :: (C.HashTable h, Eq k, Hashable k) =>
            IOHashTable h k v -> k -> v -> IO ()
insert h k v = stToIO $ C.insert h k v
{-# INLINE insert #-}
{-# SPECIALIZE INLINE insert :: (Eq k, Hashable k) => BasicHashTable  k v -> k -> v -> IO () #-}
--{-# SPECIALIZE INLINE insert :: (Eq k, Hashable k) =>
--                         LinearHashTable k v -> k -> v -> IO () #-}
{-# SPECIALIZE INLINE insert :: (Eq k, Hashable k) => CuckooHashTable k v -> k -> v -> IO () #-}

insertWeak   :: (C.HashTable h, Eq k, Hashable k) =>
            IOHashTable h k v -> k -> Weak v -> IO ()
insertWeak h k w = stToIO $ C.insertWeak h k w
{-# INLINE insertWeak #-}
{-# SPECIALIZE INLINE insertWeak :: (Eq k, Hashable k) => BasicHashTable  k v -> k -> Weak v -> IO () #-}
{-# SPECIALIZE INLINE insertWeak :: (Eq k, Hashable k) => CuckooHashTable  k v -> k -> Weak v -> IO () #-}

insertWithMkWeak   :: (C.HashTable h, Eq k, Hashable k) =>
            IOHashTable h k v -> k -> v -> MkWeak -> IO ()
insertWithMkWeak h k v mkWeak = stToIO $ C.insertWithMkWeak h k v mkWeak
{-# INLINE insertWithMkWeak #-}
{-# SPECIALIZE INLINE insertWithMkWeak :: (Eq k, Hashable k) => BasicHashTable  k v -> k -> v -> MkWeak -> IO () #-}
{-# SPECIALIZE INLINE insertWithMkWeak :: (Eq k, Hashable k) => CuckooHashTable  k v -> k -> v -> MkWeak -> IO () #-}

------------------------------------------------------------------------------
-- | See the documentation for this function in "Data.HashTable.Class#v:delete".
delete   :: (C.HashTable h, Eq k, Hashable k) =>
            IOHashTable h k v -> k -> IO ()
delete h k = stToIO $ C.delete h k
{-# INLINE delete #-}
{-# SPECIALIZE INLINE delete :: (Eq k, Hashable k) => BasicHashTable  k v -> k -> IO () #-}
--{-# SPECIALIZE INLINE delete :: (Eq k, Hashable k) => LinearHashTable k v -> k -> IO () #-}
{-# SPECIALIZE INLINE delete :: (Eq k, Hashable k) => CuckooHashTable k v -> k -> IO () #-}


------------------------------------------------------------------------------
-- | See the documentation for this function in "Data.HashTable.Class#v:lookup".
lookup   :: (C.HashTable h, Eq k, Hashable k) =>
            IOHashTable h k v -> k -> IO (Maybe v)
lookup h k = stToIO $ C.lookup h k
{-# INLINE lookup #-}
{-# SPECIALIZE INLINE lookup :: (Eq k, Hashable k) => BasicHashTable  k v -> k -> IO (Maybe v) #-}
--{-# SPECIALIZE INLINE lookup :: (Eq k, Hashable k) => LinearHashTable k v -> k -> IO (Maybe v) #-}
{-# SPECIALIZE INLINE lookup :: (Eq k, Hashable k) => CuckooHashTable k v -> k -> IO (Maybe v) #-}


------------------------------------------------------------------------------
-- | See the documentation for this function in
-- "Data.HashTable.Class#v:fromList".
fromList :: (C.HashTable h, Eq k, Hashable k) =>
            [(k,v)] -> IO (IOHashTable h k v)
fromList = stToIO . C.fromList
{-# INLINE fromList #-}
{-# SPECIALIZE INLINE fromList :: (Eq k, Hashable k) => [(k,v)] -> IO (BasicHashTable  k v) #-}
--{-# SPECIALIZE INLINE fromList :: (Eq k, Hashable k) => [(k,v)] -> IO (LinearHashTable k v) #-}
{-# SPECIALIZE INLINE fromList :: (Eq k, Hashable k) => [(k,v)] -> IO (CuckooHashTable k v) #-}


------------------------------------------------------------------------------
-- | See the documentation for this function in
-- "Data.HashTable.Class#v:fromListWithSizeHint".
fromListWithSizeHint :: (C.HashTable h, Eq k, Hashable k) =>
                        Int -> [(k,v)] -> IO (IOHashTable h k v)
fromListWithSizeHint n = stToIO . C.fromListWithSizeHint n
{-# INLINE fromListWithSizeHint #-}
{-# SPECIALIZE INLINE fromListWithSizeHint :: (Eq k, Hashable k) => Int -> [(k,v)] -> IO (BasicHashTable  k v) #-}
--{-# SPECIALIZE INLINE fromListWithSizeHint :: (Eq k, Hashable k) => Int -> [(k,v)] -> IO (LinearHashTable k v) #-}
{-# SPECIALIZE INLINE fromListWithSizeHint :: (Eq k, Hashable k) => Int -> [(k,v)] -> IO (CuckooHashTable k v) #-}


------------------------------------------------------------------------------
-- | See the documentation for this function in "Data.HashTable.Class#v:toList".
toList   :: (C.HashTable h, Eq k, Hashable k) =>
            IOHashTable h k v -> IO [(k,v)]
toList = stToIO . C.toList
{-# INLINE toList #-}
{-# SPECIALIZE INLINE toList :: (Eq k, Hashable k) => BasicHashTable  k v -> IO [(k,v)] #-}
--{-# SPECIALIZE INLINE toList :: (Eq k, Hashable k) => LinearHashTable k v -> IO [(k,v)] #-}
{-# SPECIALIZE INLINE toList :: (Eq k, Hashable k) => CuckooHashTable k v -> IO [(k,v)] #-}


------------------------------------------------------------------------------
-- | See the documentation for this function in "Data.HashTable.Class#v:foldM".
foldM :: (C.HashTable h) =>
         (a -> (k,v) -> IO a)
      -> a
      -> IOHashTable h k v -> IO a
foldM f seed ht = stToIO $ C.foldM f' seed ht
  where
    f' !i !t = unsafeIOToST $ f i t
{-# INLINE foldM #-}
{-# SPECIALIZE INLINE foldM :: (a -> (k,v) -> IO a) -> a -> BasicHashTable  k v -> IO a #-}
--{-# SPECIALIZE INLINE foldM :: (a -> (k,v) -> IO a) -> a -> LinearHashTable k v -> IO a #-}
{-# SPECIALIZE INLINE foldM :: (a -> (k,v) -> IO a) -> a -> CuckooHashTable k v -> IO a #-}

foldWeakM :: (C.HashTable h) =>
         (a -> (k,Weak v) -> IO a)
      -> a
      -> IOHashTable h k v -> IO a
foldWeakM f seed ht = stToIO $ C.foldWeakM f' seed ht
  where
    f' !i !t = unsafeIOToST $ f i t
{-# INLINE foldWeakM #-}
{-# SPECIALIZE INLINE foldWeakM :: (a -> (k,Weak v) -> IO a) -> a -> BasicHashTable  k v -> IO a #-}
{-# SPECIALIZE INLINE foldWeakM :: (a -> (k,Weak v) -> IO a) -> a -> CuckooHashTable  k v -> IO a #-}

foldStopM :: (C.HashTable h) =>
         (a -> (k,v) -> IO (Either a a))
      -> a
      -> IOHashTable h k v -> IO a
foldStopM f seed ht = stToIO $ C.foldStopM f' seed ht
  where
    f' !i !t = unsafeIOToST $ f i t
{-# INLINE foldStopM #-}
{-# SPECIALIZE INLINE foldStopM :: (a -> (k,v) -> IO (Either a a)) -> a -> BasicHashTable  k v -> IO a #-}
--{-# SPECIALIZE INLINE foldM :: (a -> (k,v) -> IO a) -> a -> LinearHashTable k v -> IO a #-}
{-# SPECIALIZE INLINE foldStopM :: (a -> (k,v) -> IO (Either a a)) -> a -> CuckooHashTable k v -> IO a #-}

------------------------------------------------------------------------------
-- | See the documentation for this function in "Data.HashTable.Class#v:mapM_".
mapM_ :: (C.HashTable h) => ((k,v) -> IO a) -> IOHashTable h k v -> IO ()
mapM_ f ht = stToIO $ C.mapM_ f' ht
  where
    f' = unsafeIOToST . f
{-# INLINE mapM_ #-}
{-# SPECIALIZE INLINE mapM_ :: ((k,v) -> IO a) -> BasicHashTable  k v -> IO () #-}
--{-# SPECIALIZE INLINE mapM_ :: ((k,v) -> IO a) -> LinearHashTable k v -> IO () #-}
{-# SPECIALIZE INLINE mapM_ :: ((k,v) -> IO a) -> CuckooHashTable k v -> IO () #-}

mapWeakM_ :: (C.HashTable h) => ((k,Weak v) -> IO a) -> IOHashTable h k v -> IO ()
mapWeakM_ f ht = stToIO $ C.mapWeakM_ f' ht
  where
    f' = unsafeIOToST . f
{-# INLINE mapWeakM_ #-}
{-# SPECIALIZE INLINE mapWeakM_ :: ((k,Weak v) -> IO a) -> BasicHashTable  k v -> IO () #-}
{-# SPECIALIZE INLINE mapWeakM_ :: ((k,Weak v) -> IO a) -> CuckooHashTable  k v -> IO () #-}

------------------------------------------------------------------------------
-- | See the documentation for this function in
-- "Data.HashTable.Class#v:computeOverhead"

computeOverhead :: (C.HashTable h) => IOHashTable h k v -> IO Double
computeOverhead = stToIO . C.computeOverhead
{-# INLINE computeOverhead #-}

finalize :: (Eq k,Hashable k,C.HashTable h) => IOHashTable h k v -> IO ()
finalize = stToIO . C.finalize
{-# INLINE finalize #-}
{-# SPECIALIZE INLINE finalize :: (Eq k,Hashable k) => BasicHashTable k v -> IO () #-}
{-# SPECIALIZE INLINE finalize :: (Eq k,Hashable k) => CuckooHashTable k v -> IO () #-}


