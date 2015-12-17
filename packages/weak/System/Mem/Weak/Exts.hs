{-# LANGUAGE Rank2Types, DeriveDataTypeable #-}
{-# LANGUAGE UndecidableInstances, MultiParamTypeClasses, FlexibleInstances, MagicHash, UnboxedTuples #-}

module System.Mem.Weak.Exts (
	  module System.Mem.Weak
	, mkDeadWeak, deadWeak, andMkWeak, orMkWeak, MkWeak(..)
	, mkWeakKeyIORef, mkWeakKeySTRef, mkWeakKeyMVar
	, WeakRef(..), WeakKey(..), mkWeakKey'
	) where

import System.Mem.Weak
import Data.Typeable
import GHC.IORef
import GHC.MVar
import GHC.Conc
import GHC.STRef
import GHC.Weak
import GHC.Base
import System.Mem.Weak as Weak
import Data.Typeable
import Control.Concurrent.MVar
import Control.Monad.ST

-- | Makes a dummy @Weak@ pointer that is already dead
mkDeadWeak v f = do
	w <- Weak.mkWeak () v f
	Weak.finalize w
	return w
	
deadWeak :: IO (Weak a)
deadWeak = mkDeadWeak (error "deadWeak") Nothing

newtype MkWeak = MkWeak { unMkWeak :: forall v . v -> Maybe (IO ()) -> IO (Weak v) } deriving Typeable

-- | Creates a weak reference that is alive as long as two keys are
-- NB: this is not completely symmetric: if the value is the same as the second key, then it will be kept alive as long as the first is alive
andMkWeak :: MkWeak -> MkWeak -> MkWeak
andMkWeak (MkWeak mkWeak1) (MkWeak mkWeak2) = MkWeak $ \v f -> do
	w1 <- mkWeak1 v f
	w2 <- mkWeak2 () (Just $! finalize w1) -- the second reference does not add a dependency from the key to the value but only a finalizer; when the second key dies, finalize the first weak reference
	return $ w2 `seq` w1

-- | Creates a weak reference that is alive as long as at least one of the keys is 
orMkWeak :: MkWeak -> MkWeak -> MkWeak
orMkWeak (MkWeak mkWeak1) (MkWeak mkWeak2) = MkWeak $ \v f -> do
	w1 <- mkWeak1 v f
	w2 <- mkWeak2 v Nothing -- the first reference cannot be dead unless the second one is, due to the value dependencies
	return $ w2 `seq` w1

-- A class for precise finalization of weak pointers.

-- Important note from the documentation of System.Mem.Weak:
-- Finalizers can be used reliably for types that are created explicitly and have identity, such as IORef and MVar. However, to place a finalizer on one of these types, you should use the specific operation provided for that type, e.g. mkWeakIORef and addMVarFinalizer respectively (the non-uniformity is accidental). These operations attach the finalizer to the primitive object inside the box (e.g. MutVar# in the case of IORef), because attaching the finalizer to the box itself fails when the outer box is optimised away by the compiler.

mkWeakKeyIORef :: IORef a -> b -> IO () -> IO (Weak b)
mkWeakKeyIORef k@(IORef (STRef r#)) v f = IO $ \s ->
  case mkWeak# r# v f s of (# s1, w #) -> (# s1, Weak w #)

mkWeakKeySTRef :: STRef s a -> b -> IO () -> IO (Weak b)
mkWeakKeySTRef k@(STRef r#) v f = IO $ \s ->
  case mkWeak# r# v f s of (# s1, w #) -> (# s1, Weak w #)

mkWeakKeyMVar :: MVar a -> b -> IO () -> IO (Weak b)
mkWeakKeyMVar m@(MVar m#) v f = IO $ \s ->
  case mkWeak# m# v f s of (# s1, w #) -> (# s1, Weak w #)

class WeakRef r where
	mkWeakRefKey :: r a -> b -> Maybe (IO ()) -> IO (Weak b)

instance WeakRef IORef where
	mkWeakRefKey = \r v mb -> mkWeakKeyIORef r v (maybe (return ()) id mb)
	{-# INLINE mkWeakRefKey #-}

instance WeakRef MVar where
	mkWeakRefKey = \r v mb -> mkWeakKeyMVar r v (maybe (return ()) id mb)
	{-# INLINE mkWeakRefKey #-}

-- | class to create weak pointers with references (typically IORef,STRef that have unique addresses) as keys
class WeakKey r where
	mkWeakKey :: r -> b -> Maybe (IO ()) -> IO (Weak b)

--instance WeakKey (HT.HashTable s k v) where
--	mkWeakKey h v mb = HT.mkWeakKey h v (maybe (return ()) id mb)

instance WeakKey (IORef a) where
	mkWeakKey = \r v mb -> mkWeakKeyIORef r v (maybe (return ()) id mb)
	{-# INLINE mkWeakKey #-}

instance WeakKey (MVar a) where
	mkWeakKey = \r v mb -> mkWeakKeyMVar r v (maybe (return ()) id mb)
	{-# INLINE mkWeakKey #-}
	
{-# INLINE mkWeakKey' #-}
mkWeakKey' :: WeakKey r => r -> Maybe (IO ()) -> IO (Weak r)
mkWeakKey' = \r f -> mkWeakKey r r f


