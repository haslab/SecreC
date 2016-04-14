module Language.Boogie.Transformation.Axiomatize where

import Language.Boogie.AST
import Language.Boogie.Position
import Language.Boogie.Exts

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State as State

import Data.Set(Set(..))
import qualified Data.Set as Set
import Data.Map(Map(..))
import qualified Data.Map as Map

type AxiomM = State AxiomSt

data AxiomSt = AxiomSt { axioms :: Set Id, globalVars :: Map Id (Type,Expression) }

axiomatizeProgram :: Program -> AxiomM Program
axiomatizeProgram (Program decls) = do
    decls' <- concatMapM axiomatizeDecl decls
    return $ Program decls'

axiomatizeDecl :: Decl -> AxiomM [Decl]
axiomatizeDecl (Pos p d) = do
    ds' <- axiomatizeBareDecl d
    return $ map (Pos p) ds'

splitContracts :: [Contract] -> ([Expression],[Id],[Expression])
splitContracts [] = ([],[],[])
splitContracts (Requires _ e:cs) = let (rs,ms,es) = splitContracts cs in (e:rs,ms,es)
splitContracts (Modifies _ vs:cs) = let (rs,ms,es) = splitContracts cs in (rs,vs++ms,es)
splitContracts (Ensures _ e:cs) = let (rs,ms,es) = splitContracts cs in (rs,ms,e:es)

findGlobalVars :: [Id] -> AxiomM ([IdType],[Expression])
findGlobalVars [] = return ([],[])
findGlobalVars (i:is) = do
    vs <- liftM globalVars State.get
    let (t,w) = (Map.!) vs i
    (its',ws') <- findGlobalVars is
    return ((i,t):its',w:ws')

axiomatizeBareDecl :: BareDecl -> AxiomM [BareDecl]
axiomatizeBareDecl d@(ProcedureDecl atts name targs args _ contracts _) = do
    axs <- liftM axioms State.get
    if Set.member name axs
        then do
            let args' = map (\itw -> (itwId itw,itwType itw)) args
            let wheres = map itwWhere args
            let (requires,modifies,ensures) = splitContracts contracts
            (gvars,gwheres) <- findGlobalVars modifies
            let ax = AxiomDecl (atts) $ Pos noPos $ Quantified Forall targs (args'++gvars) [] $ andExprs (wheres++gwheres++requires) `impliesExpr` andExprs (filter (not . hasOldExpr) ensures)
            return [d,ax]
        else return [d]
axiomatizeBareDecl d = return [d]



