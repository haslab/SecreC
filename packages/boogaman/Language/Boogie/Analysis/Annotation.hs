{-# LANGUAGE ViewPatterns #-}

module Language.Boogie.Analysis.Annotation where

import Language.Boogie.AST
import Language.Boogie.Options
import Language.Boogie.Position

import Data.List
import Data.Generics

boxE :: BareExpression -> Maybe BareExpression
boxE (Application "$Box" [e]) = Just $ unPos e
boxE e = Nothing

unboxE :: BareExpression -> Maybe BareExpression
unboxE (Application "$Unbox" [e]) = Just $ unPos e
unboxE e = Nothing

dafnyAppE :: Bool -> String -> BareExpression -> Maybe BareExpression
dafnyAppE isPoly name (unboxE -> Just e) = dafnyAppE isPoly name e
dafnyAppE isPoly name (Coercion e _) = dafnyAppE isPoly name (unPos e)
dafnyAppE isPoly name (Application ((==name) -> True) [unPos -> e]) = Just e
dafnyAppE True name (Application (isSuffixOf ("."++name) -> True) [tclass,heap,(boxE . unPos) -> Just e]) = Just e
dafnyAppE False name (Application (isSuffixOf ("."++name) -> True) [heap,(boxE . unPos) -> Just e]) = Just e
dafnyAppE isPoly name e = Nothing

isAnn :: Options -> Bool -> Id -> BareExpression -> Maybe BareExpression
isAnn opts@(vcgen -> NoVCGen) isPoly name (Application ((==name) -> True) [unPos -> e]) = Just e
isAnn opts@(vcgen -> Dafny) isPoly name (dafnyAppE isPoly name -> Just e) = Just e
isAnn opts _ _ e = Nothing

gReplaceFrees :: Data a => Options -> a -> a
gReplaceFrees opts@(vcgen -> Dafny) = everywhere (mkT (replaceFrees opts))
gReplaceFrees opts@(vcgen -> NoVCGen) = id

isFreeExpr :: Options -> BareExpression -> Maybe BareExpression
isFreeExpr vc (isAnn vc False "Free" -> Just i) = Just i
isFreeExpr vc _ = Nothing

replaceFrees :: Options -> BareExpression -> BareExpression
replaceFrees opts (isAnn opts False "Free#canCall" -> Just i) = tt
replaceFrees opts (isFreeExpr opts -> Just e) = e
replaceFrees opts e = e

gReplaceCanCall :: Data a => Options -> a -> a
gReplaceCanCall opts@(vcgen -> Dafny) = everywhere (mkT (replaceCanCall opts))
gReplaceCanCall opts@(vcgen -> NoVCGen) = id

replaceCanCall :: Options -> BareExpression -> BareExpression
replaceCanCall opts (isAnn opts True "PublicIn#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts True "PublicOut#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts True "PublicMid#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts True "Leak#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts True "DeclassifiedIn#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts True "DeclassifiedOut#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False "Leakage#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts False "Free#canCall" -> Just i) = tt
replaceCanCall opts e = e

