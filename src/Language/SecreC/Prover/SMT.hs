{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module Language.SecreC.Prover.SMT (
    module Language.SecreC.Prover.SBV
    , isValid
    ) where

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
import Control.Monad.State.Strict as State
import Control.Monad.Except

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Syntax
import Language.SecreC.Prover.Base
import Language.SecreC.Prover.SBV
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.Prover.Semantics
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint hiding (proveWith)
import Language.SecreC.Utils
import Language.SecreC.Monad
import Language.SecreC.Vars

import Text.PrettyPrint

import System.IO

--equalICond :: (VarsGTcM m,Location loc) => loc -> ICond -> ICond -> TcM m Bool
--equalICond l c1 c2 = do
--    hyp <- solveHypotheses l
--    addErrorM l (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (text "equal" <+> pp c1 <+> pp c2)) $ do
--        case (ci1,ci2) of
--            (IBool b1,IBool b2) -> return $ b1 == b2
--            otherwise -> checkAny (\cfg -> equalSBV cfg l hyp ci1 ci2) 
--
--compareICond :: (VarsGTcM m,Location loc) => loc -> ICond -> ICond -> TcM m Ordering
--compareICond l c1 c2 = do
--    hyp <- solveHypotheses l
--    addErrorM l (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (text "compare" <+> pp c1 <+> pp c2)) $ do
--        ci1 <- simplifyICond hyp c1
--        ci2 <- simplifyICond hyp c2
--        case (ci1,ci2) of
--            (IBool b1,IBool b2) -> return $ compare b1 b2
--            otherwise -> checkAny (\cfg -> compareSBV cfg l hyp ci1 ci2) 

isValid :: (ProverK loc m) => loc -> IExpr -> TcM m ()
isValid l c = do
    hyp <- solveHypotheses l
    pph <- pp $ iAnd hyp
    ppc <- pp c
    addErrorM l (TypecheckerError (locpos l) . SMTException (pph) (ppc)) $ do
        checkEvalOrSMT l (IBinOp IImplies (iAnd hyp) c) (\cfg -> checkValiditySBV l cfg (iAnd hyp) c)

-- * SBV interface
--
--compareSBV :: (VarsGTcM m,Location loc) => SMTConfig -> loc -> [ICond] -> ICond -> ICond -> TcM m Ordering
--compareSBV cfg l hyp c1 c2 = addErrorM l (TypecheckerError (locpos l) . (ComparisonException "index condition") (pp c1) (pp c2) . Just) $ do
--    let str1 = ppr (IAnd $ c1 : hyp) ++ " => " ++ ppr c2
--    let str2 = ppr (IAnd $ c2 : hyp) ++ " => " ++ ppr c1
--    lt <- tryValiditySBV l cfg str1 $ do
--        hyp2SBV l $ IAnd $ c1 : hyp
--        cond2SBV l c2
--    nlt <- tryValiditySBV l cfg str1 $ do
--        hyp2SBV l $ IAnd hyp
--        cond2SBV l $ INot $ c1 `implies` c2
--    gt <- tryValiditySBV l cfg str2 $ do
--        hyp2SBV l $ IAnd $ c2 : hyp
--        cond2SBV l c1
--    ngt <- tryValiditySBV l cfg str1 $ do
--        hyp2SBV l $ IAnd hyp
--        cond2SBV l $ INot $ c2 `implies` c1
--    case (lt,nlt,gt,ngt) of
--        (Nothing,_,Nothing,_) -> return EQ
--        (Nothing,_,_,Nothing) -> return LT
--        (_,Nothing,Nothing,_) -> return GT
--        otherwise -> genTcError (locpos l) $ text "not comparable"
--
--equalSBV :: (VarsGTcM m,Location loc) => SMTConfig -> loc -> [ICond] -> ICond -> ICond -> TcM m Bool
--equalSBV cfg l hyp c1 c2 = addErrorM l (TypecheckerError (locpos l) . (EqualityException "index condition") (pp c1) (pp c2) . Just) $ do
--    let str = show (pp c1 <+> text "==" <+> pp c2)
--    mb <- tryValiditySBV l cfg str $ do
--        hyp2SBV l $ IAnd hyp
--        s1 <- cond2SBV l c1
--        s2 <- cond2SBV l c2
--        return (s1 .== s2)
--    case mb of
--        Nothing -> return True
--        Just err -> throwError err

checkValiditySBV :: (ProverK loc m) => loc -> SMTConfig -> IExpr -> IExpr -> TcM m ()
checkValiditySBV l cfg hyp prop = do
    opts <- askOpts
    d1 <- ppM l hyp
    d2 <- ppM l prop
    let str = d1 <+> text " => " <+> d2
    r <- validitySBV l cfg (show str) $ do
        hyp2SBV l hyp
        SBool b <- iExpr2SBV l prop
        return b
    return r

--tryValiditySBV :: (MonadIO m,Location loc) => loc -> SMTConfig -> String -> TcSBV SBool -> TcM m (Maybe SecrecError)
--tryValiditySBV l cfg msg prop = (validitySBV l cfg msg prop >> return Nothing) `catchError` (return . Just)

validitySBV :: (MonadIO m,Location loc) => loc -> SMTConfig -> String -> TcSBV SBool -> TcM m ()
validitySBV l cfg str sprop = do
    opts <- askOpts
--  smt <- compileToSMTLib True False sprop
--  liftIO $ putStrLn smt
    debugTc $ do
        ppl <- ppr (locpos l)
        liftIO $ putStrLn (ppl ++ ": Calling external SMT solver " ++ show cfg ++ " to check " ++ str ++ " ... ")
    r <- proveWithTcSBV cfg sprop
    case r of
        Left err -> do
            debugTc $ liftIO $ putStrLn $ "failed: " ++ pprid err
            throwError err
        Right (ThmResult (Unsatisfiable _)) -> do
            debugTc $ liftIO $ putStrLn "ok"
        Right (ThmResult (Satisfiable _ _)) -> do
            debugTc $ liftIO $ putStrLn $ "falsifiable: " ++ show r
            genTcError (UnhelpfulPos $ show cfg) False $ text $ show r
        otherwise -> do
            debugTc $ liftIO $ putStrLn $ "failed: " ++ show r
            genTcError (UnhelpfulPos $ show cfg) True $ text $ show r

-- * Generic interface

instance Show SMTConfig where
    show _ = "SMTConfig"

supportedSolvers :: [SMTConfig]
supportedSolvers = map (defaultSolverConfig) [minBound..maxBound::Solver]

checkWithAny :: (MonadIO m) => [String] -> [SecrecError] -> [SMTConfig] -> (SMTConfig -> TcM m a) -> TcM m (Either a [SecrecError])
checkWithAny names errs [] check = return $ Right errs
checkWithAny names errs (solver:solvers) check = do
    liftM Left (check solver) `catchError` \err -> do
        checkWithAny names (errs++[err]) solvers check

checkAny :: MonadIO m => (SMTConfig -> TcM m a) -> TcM m a
checkAny check = do
    solvers <- liftIO sbvAvailableSolvers
    when (null solvers) $ genTcError noloc False $ text "No solver found"
    res <- checkWithAny (map show solvers) [] solvers check
    case res of
        Left x -> return x
        Right errs -> throwError $ MultipleErrors errs

checkEvalOrSMT :: ProverK loc m => loc -> IExpr -> (SMTConfig -> TcM m ()) -> TcM m ()
checkEvalOrSMT l ie check = do
    res <- catchError (liftM Right $ fullyEvaluateIExpr l ie) (return . Left)
    case res of
        Left err -> checkAny check
        Right (IBool True) -> return ()
        Right (IBool False) -> genTcError (UnhelpfulPos "evalIExpr") False $ text "false"
        Right ilit -> do
            ppilit <- pp ilit
            genTcError (UnhelpfulPos "evalIExpr") True $ text "not a static boolean prover expression" <+> ppilit

