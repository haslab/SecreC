{-# LANGUAGE DeriveDataTypeable #-}

module Language.Boogie.Transformation where

import Language.Boogie.Parser
import Language.Boogie.Transformation.Shadow
import Language.Boogie.Transformation.Axiomatize hiding (axioms,globalVars)
import Language.Boogie.Transformation.Leakage
import Language.Boogie.Analysis.Leakage hiding (leakage)
import qualified Language.Boogie.Transformation.Simplify as S
import Language.Boogie.AST

import Data.Set(Set(..))
import qualified Data.Set as Set
import Data.Map(Map(..))
import qualified Data.Map as Map
import Data.Data

import Control.Monad
import Control.Monad.State

import Text.ParserCombinators.Parsec (parse, parseFromFile)

import Paths_Boogaman

data VCGen
    = NoVCGen
    | Dafny
  deriving (Show, Data, Typeable,Eq)

data Options
    = Opts  { 
          input                :: FilePath
        , output               :: FilePath
        , shadow               :: Bool
        , simplify             :: Bool
        , leakage              :: Maybe Bool
        , vcgen                :: VCGen
        , axioms               :: [Id]
        }
    deriving (Show, Data, Typeable)

defaultExemptions = Set.fromList ["int","real","bool"]

getExemptions :: VCGen -> IO (Set Id,Type -> Bool)
getExemptions NoVCGen = return (defaultExemptions,const False)
getExemptions Dafny = do
    bpl <- getDataFileName "dafny.bpl"
    Right defs <- parseFromFile program bpl
    let exs = Set.unions [programDefs defs,defaultExemptions,Set.fromList ["$_reverifyPost","$_Frame"]]
    return (exs,dafnyTyExemptions)

dafnyTyExemptions :: Type -> Bool
dafnyTyExemptions (IdType "Ty" []) = True
dafnyTyExemptions t = False

transform :: Options -> Program -> IO Program
transform opts = simplifyP opts >=> leakageP opts >=> shadowP opts >=> axiomatizeP opts

simplifyP :: Options -> Program -> IO Program
simplifyP opts p = return $ if (simplify opts || shadow opts) then S.runSimplify p else p

leakageP :: Options -> Program -> IO Program
leakageP opts p = case leakage opts of
    Nothing -> return p
    Just leak -> return $ changeLeakageProgram leak p

axiomatizeP :: Options -> Program -> IO Program
axiomatizeP opts p = do
    let axs = Set.fromList $ axioms opts
    let gs = foldr (\(IdTypeWhere i t w) m -> Map.insert i (t,w) m) Map.empty $ snd $ globalVars p
    return $ evalState (axiomatizeProgram p) (AxiomSt axs gs)

shadowP :: Options -> Program -> IO Program
shadowP opts p = do
    (exemptions,tyExemptions) <- getExemptions (vcgen opts)
    return $ if shadow opts then runShadow exemptions tyExemptions p else p



