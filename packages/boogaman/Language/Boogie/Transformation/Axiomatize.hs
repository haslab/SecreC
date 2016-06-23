module Language.Boogie.Transformation.Axiomatize where

import Language.Boogie.AST
import Language.Boogie.Options
import Language.Boogie.Position
import Language.Boogie.Exts
import Language.Boogie.Analysis.Leakage

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State as State

import Data.Set(Set(..))
import qualified Data.Set as Set
import Data.Map(Map(..))
import qualified Data.Map as Map

type AxiomM = State AxiomSt

data AxiomSt = AxiomSt { pAxioms :: Set Id, pGlobalVars :: Map Id (Type,Expression) }

axiomatizeProgram :: Options -> Program -> AxiomM Program
axiomatizeProgram opts (Program decls) = do
    decls' <- concatMapM (axiomatizeDecl opts) decls
    return $ Program decls'

axiomatizeDecl :: Options -> Decl -> AxiomM [Decl]
axiomatizeDecl opts (Pos p d) = do
    ds' <- axiomatizeBareDecl opts d
    return $ map (Pos p) ds'

splitContracts :: [Contract] -> ([Expression],[Id],[Expression])
splitContracts [] = ([],[],[])
splitContracts (Requires _ e:cs) = let (rs,ms,es) = splitContracts cs in (e:rs,ms,es)
splitContracts (Modifies _ vs:cs) = let (rs,ms,es) = splitContracts cs in (rs,vs++ms,es)
splitContracts (Ensures _ e:cs) = let (rs,ms,es) = splitContracts cs in (rs,ms,e:es)

findGlobalVars :: [Id] -> AxiomM ([IdType],[Expression])
findGlobalVars [] = return ([],[])
findGlobalVars (i:is) = do
    vs <- liftM pGlobalVars State.get
    let (t,w) = (Map.!) vs i
    (its',ws') <- findGlobalVars is
    return ((i,t):its',w:ws')

axiomatizeBareDecl :: Options -> BareDecl -> AxiomM [BareDecl]
axiomatizeBareDecl opts d@(ProcedureDecl atts name targs args _ contracts _) = do
    axs <- liftM pAxioms State.get
    if Set.member name axs
        then do
            let args' = map (\itw -> (itwId itw,itwType itw)) args
            let wheres = map itwWhere args
            let (requires,modifies,ensures) = splitContracts contracts
            (gvars,gwheres) <- findGlobalVars modifies
            let leakatt = if isLeakFunName opts name then [Attribute "leakage" []] else []
            let ax = AxiomDecl (leakatt ++ atts) $ Pos noPos $ Quantified Forall targs (args'++gvars) [] $ andExprs (wheres++gwheres++requires) `impliesExpr` andExprs (filter (not . hasOldExpr) ensures)
            return [d,ax]
        else return [d]
axiomatizeBareDecl opts d = return [d]



