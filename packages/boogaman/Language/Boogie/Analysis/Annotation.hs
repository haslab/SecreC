{-# LANGUAGE ViewPatterns #-}

module Language.Boogie.Analysis.Annotation where

import Language.Boogie.AST
import Language.Boogie.Options
import Language.Boogie.Position

import Text.Regex
import Text.Read

import Data.List as List
import Data.Generics

firstRE :: String -> String -> Maybe String
firstRE re str = case matchRegexAll (mkRegex re) str of
    Just (_,match,_,_) -> Just match
    otherwise -> Nothing

isDafnyReqReads :: Options -> BareExpression -> Maybe Int
isDafnyReqReads (dafnyVCGen -> Just _) (Var (firstRE "b[$]reqreads[#][0-9]*" -> Just str)) = readMaybe (drop 11 str)
isDafnyReqReads opts _ = Nothing

isDafnyAxiom :: Bool -> String -> Bool
isDafnyAxiom withModules str = List.elem str $ concat $ map (dafnyAxioms withModules) dafnyNames

dafnyPrelude True = "_0_prelude"
dafnyPrelude False = "_module"

dafnyDestroyAnn :: Bool -> String -> String
dafnyDestroyAnn withModules name = dafnyPrelude withModules ++ "._default." ++ name ++ "$T"

dafnyDestroyAnns :: Bool -> [String]
dafnyDestroyAnns withModules = map (dafnyDestroyAnn withModules) dafnyNames

hasDafnyDestroyAnn :: Data a => Options -> a -> Bool
hasDafnyDestroyAnn (dafnyVCGen -> Just withModules) x = everything (||) (mkQ False isDestroy) x
    where
    isDestroy :: Id -> Bool
    isDestroy n = List.elem n (dafnyDestroyAnns withModules)
hasDafnyDestroyAnn opts x = False

dafnyAxioms withModules name = dafnyFrameAxioms ++ dafnyConsqAxioms
    where
    dafnyFrameAxioms = ["// frame axiom for "++dafnyPrelude withModules++".__default."++name]
    dafnyConsqAxioms = ["// consequence axiom for "++dafnyPrelude withModules++".__default."++name]

dafnyNames :: [String]
dafnyNames = ["PublicIn","PublicOut","PublicMid","DeclassifiedIn","DeclassifiedOut","Leak","Leakage","Free"]

dafnyAnns :: Bool -> [String]
dafnyAnns withModules = concat $ map dafnyAnn dafnyNames
    where
    dafnyAnn name = [dafnyPrelude withModules++".__default."++name
              ,dafnyPrelude withModules++"."++name++"#canCall"
              ,dafnyPrelude withModules++".__default."++name++"#requires"
              ,"CheckWellformed$$"++dafnyPrelude withModules++".__default."++name
              ,"CheckWellformed$$"++dafnyPrelude withModules++".__default."++name]

boxE :: BareExpression -> Maybe BareExpression
boxE (Application "$Box" [e]) = Just $ unPos e
boxE e = Just e

unboxE :: BareExpression -> Maybe BareExpression
unboxE (Application "$Unbox" [e]) = Just $ unPos e
unboxE e = Just e

dafnyAppE :: Bool -> Bool -> String -> BareExpression -> Maybe BareExpression
dafnyAppE True isPoly name (unboxE -> Just e) = dafnyAppE False isPoly name e
dafnyAppE isPolyRet isPoly name (Coercion e _) = dafnyAppE isPolyRet isPoly name (unPos e)
dafnyAppE isPolyRet isPoly name (Application ((==name) -> True) [unPos -> e]) = Just e
dafnyAppE False True name (Application (isSuffixOf ("."++name) -> True) [tclass,heap,(boxE . unPos) -> Just e]) = Just e
dafnyAppE False False name (Application (isSuffixOf ("."++name) -> True) [heap,unPos -> e]) = Just e
dafnyAppE isPolyRet isPoly name e = Nothing

isAnn :: Options -> Bool -> Bool -> Id -> BareExpression -> Maybe BareExpression
isAnn opts@(vcgen -> NoVCGen) isPolyRet isPoly name (Application ((==name) -> True) [unPos -> e]) = Just e
isAnn opts@(dafnyVCGen -> Just _) isPolyRet isPoly name (dafnyAppE isPolyRet isPoly name -> Just e) = Just e
isAnn opts _ _ _ e = Nothing

gReplaceFrees :: Data a => Options -> a -> a
gReplaceFrees opts@(dafnyVCGen -> Just _) = everywhere (mkT (replaceFrees opts))
gReplaceFrees opts@(vcgen -> NoVCGen) = id

isFreeExpr :: Options -> BareExpression -> Maybe BareExpression
isFreeExpr vc (isAnn vc False False "Free" -> Just i) = Just i
isFreeExpr vc _ = Nothing

replaceFrees :: Options -> BareExpression -> BareExpression
replaceFrees opts e = maybe e id $ replaceFreesMb opts e

replaceFreesMb :: Options -> BareExpression -> Maybe BareExpression
replaceFreesMb opts (isAnn opts False False "Free#canCall" -> Just i) = Just tt
replaceFreesMb opts (isFreeExpr opts -> Just e) = Just e
replaceFreesMb opts e = Nothing

gReplaceCanCall :: Data a => Options -> a -> a
gReplaceCanCall opts@(dafnyVCGen -> Just _) = everywhere (mkT (replaceCanCall opts))
gReplaceCanCall opts@(vcgen -> NoVCGen) = id

replaceCanCall :: Options -> BareExpression -> BareExpression
replaceCanCall opts e = maybe e id $ replaceCanCallMb opts e

replaceCanCallMb :: Options -> BareExpression -> Maybe BareExpression
replaceCanCallMb opts (isAnn opts False True "PublicIn#canCall" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "PublicOut#canCall" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "PublicMid#canCall" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "Leak#canCall" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "DeclassifiedIn#canCall" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "DeclassifiedOut#canCall" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False False "Leakage#canCall" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False False "Free#canCall" -> Just i) = Just tt

replaceCanCallMb opts (isAnn opts False True "PublicIn#requires" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "PublicOut#requires" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "PublicMid#requires" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "Leak#requires" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "DeclassifiedIn#requires" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False True "DeclassifiedOut#requires" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False False "Leakage#requires" -> Just i) = Just tt
replaceCanCallMb opts (isAnn opts False False "Free#requires" -> Just i) = Just tt

replaceCanCallMb opts e = Nothing

