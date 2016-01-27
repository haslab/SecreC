{-# LANGUAGE DeriveDataTypeable, TupleSections, TypeOperators, Rank2Types, BangPatterns, FunctionalDependencies, MultiParamTypeClasses, MagicHash, ScopedTypeVariables, GADTs, FlexibleContexts, TypeFamilies, TypeSynonymInstances, FlexibleInstances #-}

module System.Mem.Weak.Map where

-- | Implementation of weak maps using hash maps and weak pointers as presented in http://community.haskell.org/~simonmar/papers/weak.pdf.
-- | Requires the package hashtables.


import Data.IORef.Exts
import Prelude hiding (lookup,mapM_)
import qualified Prelude
import Control.Exception
import Control.Concurrent.MVar

--import Data.Atomics
import System.Mem.Weak.Exts (Weak(..),MkWeak(..),WeakKey(..))
import qualified System.Mem.Weak.Exts as Weak
import System.IO.Unsafe
import Control.Monad hiding (mapM_,foldM)
import qualified Control.Monad
import Data.Hashable

import GHC.Base
import Control.Monad.IO.Class
import Data.Unique

import Data.Strict.Tuple as Strict
import Data.HashMap.Strict (HashMap(..))
import qualified Data.HashMap.Strict as HashMap
import Data.IORef
import qualified Data.Foldable as Foldable
import Data.Strict.List as SList
import Data.Typeable


newtype WeakMap k v = WeakMap (WeakMap' k v :!: Weak (WeakMap' k v)) deriving Typeable
type WeakMap' k v = IORef (HashMap k (Weak v))

instance WeakKey (WeakMap k v) where
	mkWeakKey (WeakMap (tbl :!: _)) = Weak.mkWeakKey tbl

-- does not finalize
clean' :: WeakMap k v -> IO ()
clean' (WeakMap (tbl :!: _)) = writeIORef' tbl HashMap.empty

toMap :: (Eq k,Hashable k) => WeakMap k v -> IO (HashMap k v)
toMap (WeakMap (tbl :!: _)) = do
	xs <- readIORef tbl
	let add k w m = do
		mb <- (Weak.deRefWeak w)
		case mb of
			Nothing -> m
			Just v -> liftM (HashMap.insert k v) m
	HashMap.foldrWithKey add (return HashMap.empty) xs

{-# NOINLINE new #-}
new :: (Eq k,Hashable k) => IO (WeakMap k v)
new = do
	tbl <- newIORef HashMap.empty
	weak_tbl <- Weak.mkWeakKey tbl tbl $ Just $ table_finalizer tbl
	return $ WeakMap (tbl :!: weak_tbl)

-- without finalization
{-# NOINLINE new' #-}
new' :: (Eq k,Hashable k) => IO (WeakMap k v)
new' = do
	tbl <- newIORef HashMap.empty
	weak_tbl <- Weak.mkWeakKey tbl tbl Nothing
	return $ WeakMap (tbl :!: weak_tbl)
	
{-# NOINLINE copy' #-}
copy' :: (Eq k,Hashable k) => WeakMap k v -> IO (WeakMap k v)
copy' (WeakMap (src_tbl :!: _)) = do
	tbl <- readIORef src_tbl >>= newIORef
	weak_tbl <- Weak.mkWeakKey tbl tbl Nothing
	return $ WeakMap (tbl :!: weak_tbl)

--{-# NOINLINE newFor #-}
---- | creates a new weak table that is uniquely identified by an argument value @a@
--newFor :: (Eq k,Hashable k) => a -> IO (WeakMap k v)
--newFor a = do
--	tbl <- CMap.empty
--	let (MkWeak mkWeak) = MkWeak (mkWeakKey tbl) `orMkWeak` MkWeak (Weak.mkWeak a)
--	weak_tbl <- mkWeak tbl $ Just $ table_finalizer tbl
--	return $ WeakMap (tbl :!: weak_tbl)
--	
--newForMkWeak :: (Eq k,Hashable k) => MkWeak -> IO (WeakMap k v)
--newForMkWeak (MkWeak mkWeak) = do
--	tbl <- newIORef HashMap.empty
--	weak_tbl <- mkWeak tbl $ Just $ table_finalizer tbl
--	return $ WeakMap (tbl :!: weak_tbl)

null' :: WeakMap k v -> IO Bool
null' w_tbl@(WeakMap (tbl :!: weak_tbl)) = liftM HashMap.null $ readIORef tbl

null :: WeakMap k v -> IO Bool
null w_tbl@(WeakMap (tbl :!: weak_tbl)) = readIORef tbl >>= HashMap.foldr g (return True)
	where g w mr = do
		mb <- Weak.deRefWeak w
		case mb of
			Nothing -> mr
			Just v -> return False
	

finalize :: (Eq k,Hashable k) => WeakMap k v -> IO ()
finalize w_tbl@(WeakMap (_ :!: weak_tbl)) = do
	mb <- Weak.deRefWeak weak_tbl
	case mb of
		Nothing -> return ()
		Just weak_tbl' -> table_finalizer weak_tbl'

table_finalizer :: (Eq k,Hashable k) => WeakMap' k v -> IO ()
table_finalizer tbl = do
	pairs <- readIORef tbl
	Foldable.mapM_ Weak.finalize pairs

delete :: (Eq k,Hashable k) => WeakMap k v -> k -> IO ()
delete (WeakMap (_ :!: weak_tbl)) k = do
	mb <- Weak.deRefWeak weak_tbl
	case mb of
		Nothing -> return ()
		Just weak_tbl' -> do
			tbl <- readIORef weak_tbl'
			case HashMap.lookup k tbl of
				Nothing -> return ()
				Just w -> Weak.finalize w

insertWithMkWeak :: (Eq k,Hashable k) => WeakMap k v -> k -> v -> MkWeak -> IO ()
insertWithMkWeak w_tbl@(WeakMap (tbl :!: _)) k v (MkWeak mkWeak) = do
	weak <- mkWeak v $ Just $ deleteFinalized w_tbl k
	delete w_tbl k
	modifyIORef' tbl (HashMap.insert k weak)
	
{-# INLINE insertWeak #-}
insertWeak :: (Eq k,Hashable k) => WeakMap k v -> k -> Weak v -> IO ()
insertWeak (WeakMap (tbl :!: _)) k weak = modifyIORef' tbl (HashMap.insert k weak)

{-# INLINE insert #-}
insert :: (Eq k, Hashable k) => WeakMap k v -> k -> v -> IO ()
insert tbl !k !v = insertWithMkWeak tbl k v (MkWeak $ \v -> Weak.mkWeak v v)

-- non-overlapping union
extendWeak :: (Eq k,Hashable k) => WeakMap k v -> k -> Weak v -> IO ()
extendWeak = mergeWeak (\_ _ -> return False)

-- non-overlapping union
mergeWeak :: (Eq k,Hashable k) => (v -> v -> IO Bool) -> WeakMap k v -> k -> Weak v -> IO ()
mergeWeak doOverwrite (WeakMap (tbl :!: _)) k weak = modifyIORefM_' tbl $ \m -> do
	case HashMap.lookup k m of
		Nothing -> do
			return $ HashMap.insert k weak m
		Just w -> do
			mb <- Weak.deRefWeak w
			case mb of
				Nothing -> return $ HashMap.insert k weak m
				Just oldv -> do
					mb <- Weak.deRefWeak weak
					case mb of
						Nothing -> return m
						Just newv -> do
							b <- doOverwrite oldv newv
							if b
								then return $ HashMap.insert k weak m
								else return m

-- only deletes the entry if it is already dead
deleteFinalized :: (Eq k,Hashable k) => WeakMap k v -> k -> IO ()
deleteFinalized (WeakMap (_ :!: weak_tbl)) = finalizeEntry' weak_tbl where
	finalizeEntry' weak_tbl k = do
		mb <- Weak.deRefWeak weak_tbl
		case mb of
			Nothing -> return ()
			Just r -> modifyIORefM_' r $ \m -> do
				case HashMap.lookup k m of
					Nothing -> return m
					Just w -> do
						mb <- Weak.deRefWeak w
						case mb of
							Nothing -> return $ HashMap.delete k m
							Just x -> return m

lookup :: (Eq k,Hashable k) => WeakMap k v -> k -> IO (Maybe v)
lookup (WeakMap (tbl :!: weak_tbl)) k = do
	xs <- readIORef tbl
	let mb = HashMap.lookup k xs
	case mb of
		Nothing -> return Nothing
		Just w -> Weak.deRefWeak w

-- right-biased
-- the second @WeakMap@ is not accessed concurrently
unionWithKey :: (Ord k,Hashable k) => (v -> MkWeak) -> WeakMap k v -> WeakMap k v -> IO ()
unionWithKey getKey wmap m@(WeakMap (tbl :!: _)) = do
	xs <- liftM HashMap.toList $ readIORef tbl
	
	let go (k,w) = do
		mb <- Weak.deRefWeak w
		case mb of
			Nothing -> return ()
			Just x -> do
				let MkWeak mkWeak = getKey x
				mkWeak () (Just $ deleteFinalized wmap k)
				insertWeak wmap k w
	
	Foldable.mapM_ go xs

-- right-biased
-- the second @WeakMap@ is not accessed concurrently
-- without adding finalizers
unionWithKey' :: (Ord k,Hashable k) => WeakMap k v -> WeakMap k v -> IO ()
unionWithKey' wmap m@(WeakMap (tbl :!: _)) = do
	xs <- liftM HashMap.toList $ readIORef tbl
	
	let go (k,w) = do
		mb <- Weak.deRefWeak w
		case mb of
			Nothing -> return ()
			Just x -> insertWeak wmap k w
	
	Foldable.mapM_ go xs

--extendWithKey :: (Ord k,Hashable k) => (v -> MkWeak) -> WeakMap k v -> WeakMap k v -> IO ()
--extendWithKey = mergeWithKey (\_ _ -> return False)
--
--mergeWithKey :: (Ord k,Hashable k) => (v -> v -> IO Bool) -> (v -> MkWeak) -> WeakMap k v -> WeakMap k v -> IO ()
--mergeWithKey merge getKey wmap m@(WeakMap (tbl :!: _)) = do
--	xs <- liftM HashMap.toList $ liftIO $ readIORef tbl
--	
--	let addFinalizers (k,w) = do
--		mb <- liftIO $ Weak.deRefWeak w
--		case mb of
--			Nothing -> return ()
--			Just x -> do
--				let MkWeak mkWeak = getKey x
--				liftIO $ mkWeak () (Just $ deleteFinalized wmap k)
--				mergeWeak merge wmap k w
--	
--	Foldable.mapM_ addFinalizers xs

--purge :: (Ord k,Hashable k) => WeakMap k v -> IO ()
--purge (WeakMap (_ :!: w_map)) = purgeWeak w_map where
--	purgeWeak :: (Ord k,Hashable k) => Weak (WeakMap' k v) -> IO ()
--	purgeWeak w_map = do
--		mb <- Weak.deRefWeak w_map
--		case mb of
--			Nothing -> return ()
--			Just wm -> modifyIORefM' (\m -> Foldable.foldlM purgeMap HashMap.empty (Map.toList m)) wm
--	
--	purgeMap :: (Ord k,Hashable k) => Map k (Weak v) -> (k,Weak v) -> IO (Map k (Weak v))
--	purgeMap m (k,w) = do
--			mb <- Weak.deRefWeak w
--			case mb of
--				Nothing -> return m
--				Just v -> return $ HashMap.insert k w m

--{-# INLINE mapM'' #-}
--mapM'' :: Monad m => (forall x . IO x -> m x) -> (Weak v -> m a) -> WeakMap k v -> m [a]
--mapM'' liftIO f (WeakMap (tbl :!: _)) = liftIO (readIORef tbl) >>= Control.Monad.mapM f . HashMap.elems
--
--mapM_' :: Monad m => (forall x . IO x -> m x) -> ((k,v) -> m a) -> WeakMap k v -> m ()
--mapM_' liftIO f (WeakMap (tbl :!: _)) = liftIO (readIORef tbl) >>= Control.Monad.mapM_ g . HashMap.toList where
--	g (k,w) = do
--		mb <- liftIO $ Weak.deRefWeak w
--		case mb of
--			Nothing -> return ()
--			Just v -> f (k,v) >> return ()

foldM :: (a -> (k,v) -> IO a) -> a -> WeakMap k v -> IO a
foldM f z (WeakMap (tbl :!: _)) = readIORef tbl >>= HashMap.foldlWithKey' g (return z)
	where
	g m k w = do
		mb <- Weak.deRefWeak w
		case mb of
			Nothing -> m
			Just v -> m >>= \a -> f a (k,v)
			
foldWeakM :: (a -> (k,Weak v) -> IO a) -> a -> WeakMap k v -> IO a
foldWeakM f z (WeakMap (tbl :!: _)) = readIORef tbl >>= HashMap.foldlWithKey' g (return z)
	where
	g m k w = m >>= \a -> f a (k,w)

foldWeakGenericM :: Monad m => (forall x . IO x -> m x) -> (a -> (k,Weak v) -> m a) -> a -> WeakMap k v -> m a
foldWeakGenericM lift f z (WeakMap (tbl :!: _)) = lift (readIORef tbl) >>= HashMap.foldlWithKey' g (return z)
	where
	g m k w = m >>= \a -> f a (k,w)

forM_ :: WeakMap k v -> ((k,v) -> IO a) -> IO ()	
forM_ = flip mapM_

forGenericM_ :: MonadIO m => WeakMap k v -> ((k,v) -> m a) -> m ()	
forGenericM_ = flip mapGenericM_

mapM_ :: ((k,v) -> IO a) -> WeakMap k v -> IO ()			
mapM_ f (WeakMap (tbl :!: _)) = readIORef tbl >>= HashMap.foldrWithKey g (return ())
	where
	g k w m = do
		mb <- Weak.deRefWeak w
		case mb of
			Nothing -> m
			Just v -> f (k,v) >> m

mapGenericM_ :: MonadIO m => ((k,v) -> m a) -> WeakMap k v -> m ()			
mapGenericM_ f (WeakMap (tbl :!: _)) = liftIO (readIORef tbl) >>= HashMap.foldrWithKey g (return ())
	where
	g k w m = do
		mb <- liftIO $ Weak.deRefWeak w
		case mb of
			Nothing -> m
			Just v -> f (k,v) >> m

mapWeakM_ :: ((k,Weak v) -> IO a) -> WeakMap k v -> IO ()			
mapWeakM_ f (WeakMap (tbl :!: _)) = readIORef tbl >>= HashMap.foldrWithKey g (return ())
	where
	g k w m = f (k,w) >> m

