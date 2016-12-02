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

dafnyAppE :: String -> BareExpression -> Maybe BareExpression
dafnyAppE name (unboxE -> Just e) = dafnyAppE name e
dafnyAppE name (Coercion e _) = dafnyAppE name (unPos e)
dafnyAppE name (Application ((==name) -> True) [unPos -> e]) = Just e
dafnyAppE name (Application (isSuffixOf ("."++name) -> True) [tclass,heap,(boxE . unPos) -> Just e]) = Just e
dafnyAppE name e = Nothing

isAnn :: Options -> Id -> BareExpression -> Maybe BareExpression
isAnn opts@(vcgen -> NoVCGen) name (Application ((==name) -> True) [unPos -> e]) = Just e
isAnn opts@(vcgen -> Dafny) name (dafnyAppE name -> Just e) = Just e
isAnn opts _ e = Nothing

gReplaceFrees :: Data a => Options -> a -> a
gReplaceFrees opts@(vcgen -> Dafny) = everywhere (mkT (replaceFrees opts))
gReplaceFrees opts@(vcgen -> NoVCGen) = id

isFreeExpr :: Options -> BareExpression -> Maybe BareExpression
isFreeExpr vc (isAnn vc "Free" -> Just i) = Just i
isFreeExpr vc _ = Nothing

replaceFrees :: Options -> BareExpression -> BareExpression
replaceFrees opts (isAnn opts "Free#canCall" -> Just i) = tt
replaceFrees opts (isFreeExpr opts -> Just e) = e
replaceFrees opts e = e

gReplaceCanCall :: Data a => Options -> a -> a
gReplaceCanCall opts@(vcgen -> Dafny) = everywhere (mkT (replaceCanCall opts))
gReplaceCanCall opts@(vcgen -> NoVCGen) = id

replaceCanCall :: Options -> BareExpression -> BareExpression
replaceCanCall opts (isAnn opts "PublicIn#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts "PublicOut#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts "PublicMid#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts "Leak#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts "DeclassifiedIn#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts "DeclassifiedOut#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts "Leakage#canCall" -> Just i) = tt
replaceCanCall opts (isAnn opts "Free#canCall" -> Just i) = tt
replaceCanCall opts e = e

