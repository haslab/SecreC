module Language.SecreC.Pretty where

import Text.PrettyPrint
import Data.Foldable

class PP a where
    pp :: a -> Doc

ppr :: PP a => a -> String
ppr = show . pp

ppMb Nothing = empty
ppMb (Just x) = pp x

abrackets p = char '<' <> p <> char '>'

sepBy :: Foldable t => Doc -> t Doc -> Doc
sepBy sep ps = hsep (punctuate sep $ toList ps)

