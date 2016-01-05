{-# LANGUAGE ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.SMT where

import Data.SBV hiding ((<+>))
import qualified Data.SBV as SBV
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Generics hiding (GT)

import Control.Monad.IO.Class
import Control.Monad.Catch as Catch
import Control.Monad.Reader
import Control.Monad.Except

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.SBV
import Language.SecreC.TypeChecker.Index
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.Utils

import Text.PrettyPrint

compareICond :: Location loc => loc -> ICond VarIdentifier -> ICond VarIdentifier -> TcM loc Ordering
compareICond l c1 c2 = do
    hyp <- getHypotheses
    addErrorM (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (text "compare" <+> pp c1 <+> pp c2)) $ do
        ci1 <- simplifyICond hyp c1
        ci2 <- simplifyICond hyp c2
        case (ci1,ci2) of
            (IBool b1,IBool b2) -> return $ compare b1 b2
            otherwise -> checkAny (\cfg -> compareSBV cfg l hyp ci1 ci2) 
    
simplifyICond :: [ICond VarIdentifier] -> ICond VarIdentifier -> TcM loc (ICond VarIdentifier)
simplifyICond hyp prop = case evalICond prop of
    IBool b -> return $ IBool b
    IAnd i -> return $ fromHyp hyp i
    _ -> genericError noloc $ text "Unexpected canonical form"

isValid :: Location loc => loc -> ICond VarIdentifier -> TcM loc ()
isValid l c = do
    hyp <- getHypotheses
    b <- validIConds l [c]
    unless b $ tcError (locpos l) $ SMTException (pp $ IAnd hyp) (pp c) $ GenericError (locpos l) $ text "false"

validIConds :: Location loc => loc -> [ICond VarIdentifier] -> TcM loc Bool
validIConds l c = do
    hyp <- getHypotheses
    addErrorM (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (pp $ IAnd c)) $ do
        ci <- simplifyICond hyp (IAnd c)
        case ci of
            IBool b -> return b
            r -> checkAny (\cfg -> checkValiditySBV cfg (IAnd hyp) r)

-- * SBV interface

compareSBV :: Location loc => SMTConfig -> loc -> [ICond VarIdentifier] -> ICond VarIdentifier -> ICond VarIdentifier -> TcM loc Ordering
compareSBV cfg l hyp c1 c2 = addErrorM (TypecheckerError (locpos l) . ComparisonException (pp c1) (pp c2) . Right) $ do
    sdecls <- getDeclSBV
    lt <- validitySBV cfg sdecls $ \vs -> do
		let h = runReader (cond2SBV $ IAnd $ c1 : hyp) vs
		let p = runReader (cond2SBV c2) vs
		constrain h
		return p
    gt <- validitySBV cfg sdecls $ \vs -> do
		let h = runReader (cond2SBV $ IAnd $ c2 : hyp) vs
		let p = runReader (cond2SBV c1) vs
		constrain h
		return p
    case (lt,gt) of
        (True,True) -> return EQ
        (True,False) -> return LT
        (False,True) -> return GT

checkValiditySBV :: Location loc => SMTConfig -> ICond VarIdentifier -> ICond VarIdentifier -> TcM loc Bool
checkValiditySBV cfg hyp prop = do
	sdecls <- getDeclSBV
	r <- validitySBV cfg sdecls $ \vs -> do
		let h = runReader (cond2SBV hyp) vs
		let p = runReader (cond2SBV prop) vs
		constrain h
		return p
	return r

getDeclSBV :: Location loc => TcM loc (Symbolic SBVVars)
getDeclSBV = getIndexes >>= return . mapFoldlM worker (Map.empty,Map.empty)
    where
    worker vars v t = do
		f <- type2SBV v t
		return $ f vars

getIndexes :: Location loc => TcM loc (Map VarIdentifier Type)
getIndexes = do
    xs <- getVars GlobalScope ExprC
    return $ Map.map entryType $ Map.filter (\x -> isIndexType (entryType x)) xs

validitySBV :: SMTConfig -> Symbolic SBVVars -> (SBVVars -> Symbolic SBool) -> TcM loc Bool
validitySBV cfg sdecls prop = do
    let sprop = sdecls >>= prop
--  smt <- compileToSMTLib True False sprop
--  liftIO $ putStrLn smt
    r <- liftIO $ Catch.catch
        (liftM Left (proveWith cfg sprop))
        (\(e::SomeException) -> return $ Right $ GenericError (UnhelpfulPos $ show cfg) $ text $ show e)
    case r of
        Left (ThmResult (Unsatisfiable _)) -> return True
        Left (ThmResult (Satisfiable _ _)) -> return False
        Left otherwise -> genericError (UnhelpfulPos $ show cfg) $ text $ show r
        Right err -> throwError err

-- * Generic interface

supportedSolvers :: [SMTConfig]
supportedSolvers = map (defaultSolverConfig) [minBound..maxBound::Solver]

checkWithAny :: Location loc => [String] -> [SecrecError] -> [SMTConfig] -> (SMTConfig -> TcM loc a) -> TcM loc (Either a [SecrecError])
checkWithAny names errs [] check = return $ Right []
checkWithAny names errs (solver:solvers) check = do
    liftM Left (check solver) `catchError` \err -> do
        checkWithAny names (errs++[err]) solvers check

checkAny :: Location loc => (SMTConfig -> TcM loc a) -> TcM loc a
checkAny check = do
    solvers <- liftIO sbvAvailableSolvers
    res <- checkWithAny (map show solvers) [] solvers check
    case res of
        Left x -> return x
        Right errs -> throwError $ MultipleErrors errs

