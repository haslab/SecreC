{-# LANGUAGE DoAndIfThenElse, ViewPatterns, RankNTypes #-}

module Language.Boogie.Transformation.Axiomatize where

import Language.Boogie.AST
import Language.Boogie.Options
import Language.Boogie.Position
import Language.Boogie.Exts
import Language.Boogie.Analysis.Leakage
import Language.Boogie.Analysis.Annotation
import Language.Boogie.PrettyAST
import Language.Boogie.Pretty

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State as State

import Data.Set(Set(..))
import qualified Data.Set as Set
import Data.Map(Map(..))
import qualified Data.Map as Map
import Data.Either
import Data.Generics
import Data.List as List


type AxiomM = State AxiomSt

data AxiomSt = AxiomSt { pAxioms :: Set Id, pGlobalVars :: Map Id (Type,Expression) }

getAxiomNames :: Options -> AxiomSt -> Set Id
getAxiomNames opts st = Set.map (mkAxiomName opts) $ pAxioms st

axiomatizeProgram :: Options -> Program -> AxiomM Program
axiomatizeProgram opts (Program decls) = do
    decls' <- concatMapM (axiomatizeCommentOrDecl opts) decls
    return $ Program decls'

axiomatizeCommentOrDecl :: Options -> Either Comment Decl -> AxiomM [Either Comment Decl]
axiomatizeCommentOrDecl opts (Left c) = return [Left c]
axiomatizeCommentOrDecl opts (Right d) = do
    ds' <- axiomatizeDecl opts d
    return $ map Right ds'

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
    let (t,w) = lookupMap i vs
    (its',ws') <- findGlobalVars is
    return ((i,t):its',w:ws')

axiomatizeBareDecl :: Options -> BareDecl -> AxiomM [BareDecl]
axiomatizeBareDecl opts d@(ProcedureDecl atts name targs args _ contracts _) = do
    axs <- liftM (getAxiomNames opts) State.get
    if Set.member name axs
        then do
            let args' = map (\itw -> (itwId itw,itwType itw)) args
            let wheres = map itwWhere args
            let (requires,modifies,ensures) = splitContracts $ rights contracts
            let bvs = fvs requires `Set.union` fvs ensures `Set.union` fvs wheres
            (gvars,gwheres) <- findGlobalVars $ filter (\x -> Set.member x bvs) modifies
            let leakatt = if isLeakFunName opts name then [Attribute "leakage" []] else []
            trgs <- genAxiomTriggers (args'++gvars) (requires,ensures,wheres,gwheres)
            let ax = AxiomDecl (leakatt ++ atts) $ Pos noPos $ Quantified Forall targs (args'++gvars) trgs $ andExprs (wheres++gwheres++requires) `impliesExpr` andExprs (filter (not . hasOldExpr) ensures)
            return [ax]
        else return [d]
axiomatizeBareDecl opts d = return [d]

-- generates axiom triggers for untriggered variables
genAxiomTriggers :: Data a => [IdType] -> a -> AxiomM [QTriggerAttribute]
genAxiomTriggers frees x = do
    let (_,es,_) = State.execState (collectTrgs (Set.fromList $ map fst frees) x) emptyTrgR
    return $ [Left $ Set.toList es]

type TrgM = State (Set Id,Set Expression,Set Id) ()

emptyTrgR = (Set.empty,Set.empty,Set.empty)
seqTrgMs :: [TrgM] -> TrgM
seqTrgMs [] = return ()
seqTrgMs (m:ms) = do
    m
    (bvs,es,vvs) <- State.get
    State.put (bvs,es,Set.empty)
    seqTrgMs ms
    State.modify $ \(bvs',es',vvs') -> (bvs',es',vvs `Set.union` vvs')

collectTrgs :: Data a => Set Id -> a -> TrgM
collectTrgs vs x = do
    seqTrgMs $ gmapQ (collectTrgs vs) x
    collect x
  where
    collect :: GenericQ TrgM
    collect = mkQ (return ()) (collectTrgExpr vs)

isTrgExpr :: Expression -> Bool
isTrgExpr (Pos _ (Application {})) = True
--isTrgExpr (Pos _ (UnaryExpression {})) = True
--isTrgExpr (Pos _ (BinaryExpression {})) = True
isTrgExpr e = False

-- simple trigger inference
collectTrgExpr :: Set Id -> Expression -> TrgM
collectTrgExpr vs (Pos _ (Old e)) = collectTrgExpr vs e
collectTrgExpr vs e@(isTrgExpr -> False) = do
    State.modify $ \(bvs,es,vvs) -> (bvs,es,fvs e `Set.union` vvs)
collectTrgExpr vs e@(isTrgExpr -> True) = do
    (bvs,es,vvs) <- State.get
    if Set.null (Set.difference vs bvs)
        then return ()
    else if Set.null (Set.intersection vs $ Set.difference vvs bvs)
        then return ()
    else State.put (Set.union bvs vvs,Set.insert e es,Set.empty)






