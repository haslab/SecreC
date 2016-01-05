module Language.SecreC.Pretty where

import Text.PrettyPrint
import Text.Ordinal

import Data.Foldable
import Data.Int
import Data.Word
import Data.Generics hiding (empty,GT)

class PP a where
    pp :: a -> Doc

ppr :: PP a => a -> String
ppr = show . pp

ppOpt :: Maybe a -> (a -> Doc) -> Doc
ppOpt Nothing f = empty
ppOpt (Just x) f = f x

ppMb :: PP a => Maybe a -> Doc
ppMb = flip ppOpt pp

abrackets p = char '<' <> p <> char '>'

sepBy :: Foldable t => Doc -> t Doc -> Doc
sepBy sep ps = hsep (punctuate sep $ toList ps)

ppOrdinal :: (Show a,Integral a) => a -> Doc
ppOrdinal = text . show . showOrdinal

instance PP Doc where
    pp = id
    
instance PP Ordering where
    pp EQ = text "="
    pp LT = text "<"
    pp GT = text ">"

instance PP a => PP (Maybe a) where
    pp Nothing = empty
    pp (Just x) = pp x

instance PP Integer where
    pp = integer

instance PP Int where
    pp = int

instance PP Int64 where
    pp = text . show

instance PP Word64 where
    pp = text . show

instance PP () where
    pp () = empty

instance Data Doc where
    gunfold = error "gunfold Doc"
    toConstr = error "toConstr Doc"
    dataTypeOf = error "dataTypeOf Doc"

instance Ord Doc where
    compare x y = compare (show x) (show y)

instance PP Bool where
    pp b = text (show b)