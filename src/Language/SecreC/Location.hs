{-# LANGUAGE DeriveFunctor, UndecidableInstances, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeFamilies, DeriveDataTypeable #-}

module Language.SecreC.Location where
    
import Data.Generics
    
import Language.SecreC.Pretty
import Language.SecreC.Position
import Language.SecreC.Utils

import Safe

class Location (LocOf a) => Located a where
    type LocOf a :: *
    -- | Returns the top location
    loc :: a -> (LocOf a)
    -- updates the top location
    updLoc :: a -> LocOf a -> a

class Location loc where
    locpos :: loc -> Position
    -- | Default location
    noloc :: loc
    updpos :: loc -> Position -> loc
    
instance Location Position where
    locpos = id
    noloc = UnhelpfulPos "no position info"
    updpos _ p = p
    
instance Location () where
    locpos () = noloc
    noloc = ()
    updpos _ p = ()
    
data Loc loc a = Loc loc a
  deriving (Read,Show,Data,Typeable,Functor)
 
instance Eq a => Eq (Loc loc a) where
    (Loc _ x) == (Loc _ y) = x == y
    
instance Ord a => Ord (Loc loc a) where
    compare (Loc _ x) (Loc _ y) = compare x y
 
mapLoc :: (loc1 -> loc2) -> Loc loc1 a -> Loc loc2 a
mapLoc f (Loc l1 x) = Loc (f l1) x
 
unLoc :: Loc loc a -> a
unLoc (Loc _ a) = a
 
instance PP a => PP (Loc loc a) where
    pp (Loc _ a) = pp a

instance Location loc => Located (Loc loc a) where
    type LocOf (Loc loc a) = loc
    loc (Loc l _) = l
    updLoc (Loc _ x) l = Loc l x

instance Located a => Located (NeList a) where
    type LocOf (NeList a) = LocOf a
    loc = loc . headNe
    updLoc x l = updHeadNe (flip updLoc l) x

instance Located a => Located (SepList sep a) where
    type LocOf (SepList sep a) = LocOf a
    loc = loc . headSep
    updLoc x l = updHeadSep (flip updLoc l) x
    
    
