
module Data.IORef.Exts (
	  module Data.IORef
	, readIORef', writeIORef', newIORef'
	, modifyIORefM_', modifyIORefM, modifyIORefM'
	, copyIORef'
	) where

import Data.IORef

{-# INLINE readIORef' #-}
readIORef' :: IORef a -> IO a
readIORef' r = readIORef r >>= \x -> return $! x

{-# INLINE writeIORef' #-}
writeIORef' :: IORef a -> a -> IO ()
writeIORef' r x = x `seq` writeIORef r x

{-# INLINE newIORef' #-}
newIORef' :: a -> IO (IORef a)
newIORef' x = x `seq` newIORef x

{-# INLINE copyIORef' #-}
copyIORef' :: IORef a -> IO (IORef a)
copyIORef' r = readIORef r >>= \x -> newIORef $! x

{-# INLINE modifyIORefM_' #-}
modifyIORefM_' :: IORef a -> (a -> IO a) -> IO ()
modifyIORefM_' ref f = do
    x <- readIORef ref
    x' <- f x
    x' `seq` writeIORef ref x'

{-# INLINE modifyIORefM #-}
modifyIORefM :: IORef a -> (a -> IO (a,b)) -> IO b
modifyIORefM r f = do
	x <- readIORef r
	(x',y) <- f x
	writeIORef r x'
	return y

{-# INLINE modifyIORefM' #-}
modifyIORefM' :: IORef a -> (a -> IO (a,b)) -> IO b
modifyIORefM' ref f = do
    b <- modifyIORefM ref $ \a -> f a >>= \r -> 
            case r of
                v@(a',_) -> a' `seq` return v
    b `seq` return b