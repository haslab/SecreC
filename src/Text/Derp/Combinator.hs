module Text.Derp.Combinator
 ( (<~), (~>), (<+>)
 , count, between, option, optionMaybe
 , many, many1, skipMany, skipMany1
 , sepBy, sepBy1, endBy, endBy1, endSepBy, endSepBy1, manyTill
 ) where
import Text.Derp -- hiding (xsR, xsL, xsIn, parens, parensIn
                 --        , amb, ambIn, sexp, sexpIn
                 --        )

-- import qualified Data.Set as S

tok s = Token s s

infixr 4 <~
infixl 4 ~>
a <~ b = a <~> b ==> fst
a ~> b = a <~> b ==> snd

-- choice

count :: (Ord t,Ord a) => Int -> Parser t a -> Parser t [a]
count n p | n > 0     = p <~> count (n-1) p ==> uncurry (:)
          | otherwise = eps []

-- runParse (count 2 (ter "a")) (map tok ["a","a"]) == S.fromList [["a","a"]]

between :: (Ord t,Ord open, Ord close, Ord a) =>
           Parser t open -> Parser t close -> Parser t a -> Parser t a
between open close p = open ~> (p <~ close)

-- runParse (between (ter "(") (ter ")") (many1 $ ter "a")) (map tok ["(","a","a",")"]) == S.fromList [["a","a"]]

option :: (Ord t,Ord a) => a -> Parser t a -> Parser t a
option a p = eps a <|> p

optionMaybe :: (Ord t,Ord a) => Parser t a -> Parser t (Maybe a)
optionMaybe p = eps Nothing <|> (p ==> Just)

-- optional -- what would this even mean?

many, many1 :: (Ord t,Ord a) => Parser t a -> Parser t [a]
many p = eps [] <|> many1 p
many1 p = p <~> many p ==> uncurry (:)

skipMany, skipMany1 :: (Ord t,Ord a) => Parser t a -> Parser t ()
skipMany p = eps () <|> skipMany1 p
skipMany1 p = p ~> skipMany p

sepBy, sepBy1 :: (Ord t,Ord a, Ord sep) => Parser t a -> Parser t sep -> Parser t [a]
sepBy p sep = eps [] <|> sepBy1 p sep
sepBy1 p sep = p <~> option [] (sep ~> sepBy1 p sep) ==> uncurry (:)

endBy, endBy1 :: (Ord t,Ord a, Ord sep) => Parser t a -> Parser t sep -> Parser t [a]
endBy p sep = eps [] <|> endBy1 p sep
endBy1 p sep = (p <~ sep) <~> endBy p sep ==> uncurry (:)

endSepBy, endSepBy1 :: (Ord t,Ord a, Ord sep) => Parser t a -> Parser t sep -> Parser t [a]
endSepBy p sep = eps [] <|> endSepBy1 p sep
endSepBy1 p sep = sepBy1 p sep <~ optionMaybe sep

manyTill :: (Ord t,Ord a, Ord end) => Parser t a -> Parser t end -> Parser t [a]
manyTill p end = many p <~ end

-- chainl
-- chainr
-- chainl1
-- chainr1
-- eof
-- lookAhead -- this is not meaningul in derp
-- anyToken


    
infixr 1 <+>
(<+>) :: (Ord t,Ord a,Ord b) => Parser t a -> Parser t b -> Parser t (Either a b)
p1 <+> p2 = p1 ==> Left <|> p2 ==> Right

