
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.SecreC.Position where

import Control.Monad

import Data.Foldable
import Data.Traversable
import Data.Generics (Data, Typeable)

-- | Source position
--
data Position
    -- | Normal position line:col - offset
    = Pos    !String  -- filename
             !Int     -- line number
             !Int     -- column number
             !Int     -- offset
    -- | General information
    | UnhelpfulPos String
    deriving (Read, Eq, Ord, Data, Typeable)

instance Show Position where
    show (Pos file line col off) = "file" ++ show file ++ " line " ++ show line ++ " column " ++ show col ++ " offset " ++ show off

-- | Create a 'Position'
--
{-# INLINE pos #-}
pos :: String -> Int -> Int -> Int -> Position
pos = Pos

-- | Create default 'Position'
--
defPos :: Position
defPos = UnhelpfulPos "<no location info>"
    
