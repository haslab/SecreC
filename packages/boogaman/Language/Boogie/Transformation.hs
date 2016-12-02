{-# LANGUAGE ViewPatterns, DeriveDataTypeable #-}

module Language.Boogie.Transformation where

import Language.Boogie.Parser
import Language.Boogie.Transformation.Shadow
import Language.Boogie.Transformation.Axiomatize hiding (axioms,globalVars)
import Language.Boogie.Transformation.Leakage
import Language.Boogie.Analysis.Leakage hiding (leakage)
import qualified Language.Boogie.Transformation.Simplify as S
import Language.Boogie.AST
import Language.Boogie.Options

import Data.Set(Set(..))
import qualified Data.Set as Set
import Data.Map(Map(..))
import qualified Data.Map as Map
import Data.Data
import Data.List.Split
import Data.List

import Control.Monad
import Control.Monad.State

import Text.ParserCombinators.Parsec (parse, parseFromFile)
import Text.Regex
import Text.PrettyPrint.ANSI.Leijen

import System.IO

defaultExemptions = Set.fromList ["int","real","bool"]

getExemptions :: Options -> VCGen -> Program -> IO (Set Id,Type -> Bool)
getExemptions opts NoVCGen p = return (defaultExemptions,const False)
getExemptions opts Dafny p = do
    --bpl <- getDataFileName "dafny.bpl"
    --Right defs <- parseFromFile program bpl
    let defs = programDefs p
    let pdefs = Set.filter (\x -> noUserModule x || isClassDafnyId x) defs
    --putStrLn $ "exemptions: " ++ show pdefs
    --putStrLn $ "\nno exemptions: " ++ show nos
    let exs = Set.unions [pdefs,defaultExemptions,Set.fromList ["$_reverifyPost"]]
    strace opts (show $ text "getExemptions" <+> pretty (Set.toList exs)) $ return (exs,dafnyTyExemptions)

dafnyTyExemptions :: Type -> Bool
dafnyTyExemptions (IdType "Ty" []) = True
dafnyTyExemptions t = False

noUserModule x = case dafnyIdModule x of
    Nothing -> True
    Just "prelude" -> True
    otherwise -> False

isClassDafnyId :: Id -> Bool
isClassDafnyId (isPrefixOf "class." -> True) = True
isClassDafnyId (isPrefixOf "Tagclass." -> True) = True
isClassDafnyId (isPrefixOf "Tclass." -> True) = True
isClassDafnyId (isPrefixOf "_System." -> True) = True
isClassDafnyId _ = False

-- parses the module name from a Boogie id generated by Dafny
dafnyIdModule :: Id -> Maybe String
dafnyIdModule (firstRE "[$.#]_[0-9]+_[0-9a-zA-Z]*\\." -> Just m) = Just $ (!!1) $ splitOn "_" $ init $ tail $ tail m
dafnyIdModule (firstRE "[$.#][0-9a-zA-Z]*\\." -> Just m) = Just $ init $ tail m
dafnyIdModule (firstRE "^_[0-9]+_[0-9a-zA-Z]*\\." -> Just m) = Just $ (!!1) $ splitOn "_" $ init $ tail m
dafnyIdModule (firstRE "^[0-9a-zA-Z]*\\." -> Just m) = Just $ init m
dafnyIdModule _ = Nothing

firstRE :: String -> String -> Maybe String
firstRE re str = case matchRegexAll (mkRegex re) str of
    Just (_,match,_,_) -> Just match
    otherwise -> Nothing

transform :: Options -> Program -> IO Program
transform opts = simplifyP opts >=> leakageP opts >=> axiomatizeP opts >=> shadowP opts

simplifyP :: Options -> Program -> IO Program
simplifyP opts p = return $ if (simplify opts || shadow opts) then S.runSimplify opts p else p

leakageP :: Options -> Program -> IO Program
leakageP opts p = case filterLeakage opts of
    Nothing -> return p
    Just leak -> return $ changeLeakageProgram opts leak p

axiomatizeP :: Options -> Program -> IO Program
axiomatizeP opts p = do
    let axs = Set.fromList $ axioms opts
    let gs = foldr (\(IdTypeWhere i t w) m -> Map.insert i (t,w) m) Map.empty $ snd $ globalVars p
    return $ evalState (axiomatizeProgram opts p) (AxiomSt axs gs)

shadowP :: Options -> Program -> IO Program
shadowP opts p = do
    (exemptions,tyExemptions) <- getExemptions opts (vcgen opts) p
    if shadow opts
        then runShadow opts exemptions tyExemptions p
        else return p



