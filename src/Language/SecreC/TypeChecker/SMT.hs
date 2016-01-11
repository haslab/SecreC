{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.SMT where

import Data.SBV hiding ((<+>))
import qualified Data.SBV as SBV
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Generics hiding (GT)

import Control.Monad.IO.Class
import Control.Monad.Catch as Catch
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Except

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Syntax
import Language.SecreC.TypeChecker.SBV
import Language.SecreC.TypeChecker.Index
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint hiding (proveWith)
import Language.SecreC.Utils
import Language.SecreC.Monad
import Language.SecreC.Vars

import Text.PrettyPrint

import System.IO

compareICond :: (Vars (TcM loc) loc,Location loc) => loc -> ICond VarIdentifier -> ICond VarIdentifier -> TcM loc Ordering
compareICond l c1 c2 = do
    hyp <- solveHypotheses
    addErrorM (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (text "compare" <+> pp c1 <+> pp c2)) $ do
        ci1 <- simplifyICond hyp c1
        ci2 <- simplifyICond hyp c2
        case (ci1,ci2) of
            (IBool b1,IBool b2) -> return $ compare b1 b2
            otherwise -> checkAny (\cfg -> compareSBV cfg l hyp ci1 ci2) 
    
simplifyICond :: Location loc => [ICond VarIdentifier] -> ICond VarIdentifier -> TcM loc (ICond VarIdentifier)
simplifyICond hyp prop = case evalICond prop of
    IBool b -> return $ IBool b
    IAnd i -> return $ fromHyp hyp i
    _ -> genTcError noloc $ text "Unexpected canonical form"

isValid :: (Vars (TcM loc) loc,Location loc) => loc -> ICond VarIdentifier -> TcM loc ()
isValid l c = validIConds l [c]

validIConds :: (Vars (TcM loc) loc,Location loc) => loc -> [ICond VarIdentifier] -> TcM loc ()
validIConds l c = do
    hyp <- solveHypotheses
    addErrorM (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (pp $ IAnd c)) $ do
        ci <- simplifyICond hyp (IAnd c)
        case ci of
            IBool b -> unless b $ genTcError (locpos l) $ text "false"
            r -> checkAny (\cfg -> checkValiditySBV l cfg (IAnd hyp) r)

-- * SBV interface

compareSBV :: (Vars (TcM loc) loc,Location loc) => SMTConfig -> loc -> [ICond VarIdentifier] -> ICond VarIdentifier -> ICond VarIdentifier -> TcM loc Ordering
compareSBV cfg l hyp c1 c2 = addErrorM (TypecheckerError (locpos l) . ComparisonException (pp c1) (pp c2) . Right) $ do
    let str1 = ppr (IAnd $ c1 : hyp) ++ " => " ++ ppr c2
    let str2 = ppr (IAnd $ c2 : hyp) ++ " => " ++ ppr c1
    vsh <- fvIds $ IAnd hyp
    vs1 <- fvIds c1
    vs2 <- fvIds c2
    sdecls <- getDeclSBV l (Set.unions [vsh,vs1,vs2])
    lt <- tryValiditySBV l cfg str1 sdecls $ \vs -> do
		let h = runReader (cond2SBV l $ IAnd $ c1 : hyp) vs
		let p = runReader (cond2SBV l c2) vs
		constrain h
		return p
    nlt <- tryValiditySBV l cfg str1 sdecls $ \vs -> do
		let h = runReader (cond2SBV l $ IAnd hyp) vs
		let p = runReader (cond2SBV l $ INot $ c1 `implies` c2) vs
		constrain h
		return p
    gt <- tryValiditySBV l cfg str2 sdecls $ \vs -> do
		let h = runReader (cond2SBV l $ IAnd $ c2 : hyp) vs
		let p = runReader (cond2SBV l c1) vs
		constrain h
		return p
    ngt <- tryValiditySBV l cfg str1 sdecls $ \vs -> do
		let h = runReader (cond2SBV l $ IAnd hyp) vs
		let p = runReader (cond2SBV l $ INot $ c2 `implies` c1) vs
		constrain h
		return p
    case (lt,nlt,gt,ngt) of
        (Nothing,_,Nothing,_) -> return EQ
        (Nothing,_,_,Nothing) -> return LT
        (_,Nothing,Nothing,_) -> return GT
        otherwise -> genTcError (locpos l) $ text "not comparable"

checkValiditySBV :: (Vars (TcM loc) loc,Location loc) => loc -> SMTConfig -> ICond VarIdentifier -> ICond VarIdentifier -> TcM loc ()
checkValiditySBV l cfg hyp prop = do
    let str = ppr hyp ++ " => " ++ ppr prop
    vs1 <- fvIds hyp
    vs2 <- fvIds prop
    sdecls <- getDeclSBV l (vs1 `Set.union` vs2)
    r <- validitySBV l cfg str sdecls $ \vs -> do
        let h = runReader (cond2SBV l hyp) vs
        let p = runReader (cond2SBV l prop) vs
        constrain h
        return p
    return r

getDeclSBV :: (Vars (TcM loc) loc,Location loc) => loc -> Set VarIdentifier -> TcM loc (Symbolic SBVVars)
getDeclSBV l vars = do
    ixs <- getIndexes vars
    mapFoldlM worker (return (Map.empty,Map.empty)) ixs
  where
    worker mvars v t = do
        mf <- type2SBV l v t
        return $ do
            vars <- mvars
            f <- mf
            return $ f vars

getIndexes :: Location loc => Set VarIdentifier -> TcM loc (Map VarIdentifier Type)
getIndexes ks = do
    env <- State.get
    let ss = tSubsts $ mconcatNe $ tDict env
    let vs = vars env
    let m = Map.union (Map.mapKeys (\(VarName _ k) -> k) ss) (Map.map (entryType) vs)
    return $ Map.intersection m (Map.fromSet (const $ NoType "") ks)

tryValiditySBV :: Location loc => loc -> SMTConfig -> String -> Symbolic SBVVars -> (SBVVars -> Symbolic SBool) -> TcM loc (Maybe SecrecError)
tryValiditySBV l cfg msg sdecls prop = (validitySBV l cfg msg sdecls prop >> return Nothing) `catchError` (return . Just)

validitySBV :: Location loc => loc -> SMTConfig -> String -> Symbolic SBVVars -> (SBVVars -> Symbolic SBool) -> TcM loc ()
validitySBV l cfg str sdecls prop = do
    opts <- TcM $ State.lift Reader.ask
    when (debugTypechecker opts) $
        liftIO $ hPutStrLn stderr (ppr (locpos l) ++ ": Calling external SMT solver " ++ show cfg ++ " to check " ++ str)
    let sprop = sdecls >>= prop
--  smt <- compileToSMTLib True False sprop
--  liftIO $ putStrLn smt
    r <- liftIO $ Catch.catch
        (liftM Left $ proveWith cfg sprop)
        (\(e::SomeException) -> return $ Right $ GenericError (UnhelpfulPos $ show cfg) $ text $ show e)
    case r of
        Left (ThmResult (Unsatisfiable _)) -> return ()
        Left (ThmResult (Satisfiable _ _)) -> genTcError (UnhelpfulPos $ show cfg) $ text $ show r
        Left otherwise -> genTcError (UnhelpfulPos $ show cfg) $ text $ show r
        Right err -> throwTcError err

-- * Generic interface

supportedSolvers :: [SMTConfig]
supportedSolvers = map (defaultSolverConfig) [minBound..maxBound::Solver]

checkWithAny :: Location loc => [String] -> [SecrecError] -> [SMTConfig] -> (SMTConfig -> TcM loc a) -> TcM loc (Either a [SecrecError])
checkWithAny names errs [] check = return $ Right errs
checkWithAny names errs (solver:solvers) check = do
    liftM Left (check solver) `catchError` \err -> do
        checkWithAny names (errs++[err]) solvers check

checkAny :: Location loc => (SMTConfig -> TcM loc a) -> TcM loc a
checkAny check = do
    solvers <- liftIO sbvAvailableSolvers
    when (null solvers) $ genTcError noloc $ text "No solver found"
    res <- checkWithAny (map show solvers) [] solvers check
    case res of
        Left x -> return x
        Right errs -> throwError $ MultipleErrors errs

