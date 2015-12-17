{-# LANGUAGE DeriveDataTypeable #-}

module Data.Strict.List where

import Prelude hiding (mapM,mapM_,map,sequence,length)
import Data.Typeable
import Data.Foldable as Foldable hiding (length)

-- | A strict list datatype
data List a = Cons !a !(List a) | Nil deriving (Show,Eq,Ord,Typeable)

instance Foldable List where
	{-# INLINE [0] foldr #-}
	foldr k z = go
	          where
	            go Nil     = z
	            go (Cons y ys) = y `k` go ys

last :: List a -> a
last (Cons x Nil) = x
last (Cons x xs) = Data.Strict.List.last xs

head :: List a -> a
head (Cons x _) = x

map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

mapM :: Monad m => (a -> m b) -> List a -> m (List b)
mapM f Nil = return Nil
mapM f (Cons a as) = do
	b <- f a
	bs <- mapM f as
	return $ Cons b bs

sequence :: Monad m => List (m a) -> m (List a)
sequence Nil = return Nil
sequence (Cons m ms) = do
	x <- m
	xs <- sequence ms
	return $ Cons x xs

reverse :: List a -> List a
reverse = Foldable.foldl' (flip Cons) Nil

null :: List a -> Bool
null Nil = True
null (Cons _ _) = False

length :: List a -> Int
length Nil = 0
length (Cons _ xs) = succ (length xs)

