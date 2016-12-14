{-# LANGUAGE ViewPatterns #-}

module Language.Boogie.Analysis.Annotation where

import Language.Boogie.AST
import Language.Boogie.Options
import Language.Boogie.Position

import Data.List
import Data.Generics

dafnyAnns :: [String]
dafnyAnns = concat $ map dafnyAnn ["PublicIn","PublicOut","PublicMid","DeclassifiedIn","DeclassifiedOut","Leak","Leakage","Free"]
    where
    dafnyAnn name = ["_0_prelude.__default."++name
              ,"_0_prelude.__default."++name++"#canCall"
              ,"_0_prelude.__default."++name++"#requires"
              ,"CheckWellformed$$_0_prelude.__default."++name
              ,"CheckWellformed$$_0_prelude.__default."++name]

boxE :: BareExpression -> Maybe BareExpression
boxE (Application "$Box" [e]) = Just $ unPos e
boxE e = Nothing

unboxE :: BareExpression -> Maybe BareExpression
unboxE (Application "$Unbox" [e]) = Just $ unPos e
unboxE e = Nothing

dafnyAppE :: Bool -> Bool -> String -> BareExpression -> Maybe BareExpression
dafnyAppE True isPoly name (unboxE -> Just e) = dafnyAppE False isPoly name e
dafnyAppE isPolyRet isPoly name (Coercion e _) = dafnyAppE isPolyRet isPoly name (unPos e)
dafnyAppE isPolyRet isPoly name (Application ((==name) -> True) [unPos -> e]) = Just e
dafnyAppE False True name (Application (isSuffixOf ("."++name) -> True) [tclass,heap,(boxE . unPos) -> Just e]) = Just e
dafnyAppE False False name (Application (isSuffixOf ("."++name) -> True) [heap,unPos -> e]) = Just e
dafnyAppE isPolyRet isPoly name e = Nothing

isAnn :: Options -> Bool -> Bool -> Id -> BareExpression -> Maybe BareExpression
isAnn opts@(vcgen -> NoVCGen) isPolyRet isPoly name (Application ((==name) -> True) [unPos -> e]) = Just e
isAnn opts@(vcgen -> Dafny) isPolyRet isPoly name (dafnyAppE isPolyRet isPoly name -> Just e) = Just e
isAnn opts _ _ _ e = Nothing

gReplaceFrees :: Data a => Options -> a -> a
gReplaceFrees opts@(vcgen -> Dafny) = everywhere (mkT (replaceFrees opts))
gReplaceFrees opts@(vcgen -> NoVCGen) = id

isFreeExpr :: Options -> BareExpression -> Maybe BareExpression
isFreeExpr vc (isAnn vc False False "Free" -> Just i) = Just i
isFreeExpr vc _ = Nothing

replaceFrees :: Options -> BareExpression -> BareExpression
replaceFrees opts (isAnn opts False False "Free#canCall" -> Just i) = tt
replaceFrees opts (isFreeExpr opts -> Just e) = e
replaceFrees opts e = e

gReplaceCanCall :: Data a => Options -> a -> a
gReplaceCanCall opts@(vcgen -> Dafny) = everywhere (mkT (replaceCanCall opts))
gReplaceCanCall opts@(vcgen -> NoVCGen) = id

replaceCanCall :: Options -> BareExpression -> BareExpression
replaceCanCall opts (isAnn opts False True "PublicIn#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False True "PublicOut#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False True "PublicMid#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False True "Leak#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False True "DeclassifiedIn#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False True "DeclassifiedOut#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False False "Leakage#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False False "Free#canCall" -> Just i) = tt
replaceCanCall opts e = e

