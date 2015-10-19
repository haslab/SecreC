
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Language.SecreC.Position where

import Control.Monad

import Data.Foldable
import Data.Traversable
import Data.Generics (Data, Typeable)

import Text.Parsec.Pos
import Text.PrettyPrint

import Language.SecreC.Pretty

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

instance PP Position where
    pp (Pos file line col off) = text file <> char ':' <> int line <> char ':' <> int col <> char ':' <> int off

instance Show Position where
    show (Pos file line col off) = "file " ++ show file ++ " line " ++ show line ++ " column " ++ show col ++ " offset " ++ show off

-- | Create a 'Position'
--
{-# INLINE pos #-}
pos :: String -> Int -> Int -> Int -> Position
pos = Pos

positionToSourcePos :: Position -> SourcePos
positionToSourcePos (Pos f l c o) = newPos f l c

-- | Create default 'Position'
--
defPos :: Position
defPos = UnhelpfulPos "<no location info>"
    
posFileName :: Position -> String
posFileName (Pos fn _ _ _) = fn
posFileName (UnhelpfulPos str) = error "no file name"
