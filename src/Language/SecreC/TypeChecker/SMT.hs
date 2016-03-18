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

equalICond :: (VarsIdTcM loc m,Location loc) => loc -> ICond -> ICond -> TcM loc m Bool
equalICond l c1 c2 = do
    hyp <- solveHypotheses l
    addErrorM l (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (text "equal" <+> pp c1 <+> pp c2)) $ do
        ci1 <- simplifyICond hyp c1
        ci2 <- simplifyICond hyp c2
        case (ci1,ci2) of
            (IBool b1,IBool b2) -> return $ b1 == b2
            otherwise -> checkAny (\cfg -> equalSBV cfg l hyp ci1 ci2) 

compareICond :: (VarsIdTcM loc m,Location loc) => loc -> ICond -> ICond -> TcM loc m Ordering
compareICond l c1 c2 = do
    hyp <- solveHypotheses l
    addErrorM l (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (text "compare" <+> pp c1 <+> pp c2)) $ do
        ci1 <- simplifyICond hyp c1
        ci2 <- simplifyICond hyp c2
        case (ci1,ci2) of
            (IBool b1,IBool b2) -> return $ compare b1 b2
            otherwise -> checkAny (\cfg -> compareSBV cfg l hyp ci1 ci2) 
    
simplifyICond :: (MonadIO m,Location loc) => [ICond] -> ICond -> TcM loc m (ICond)
simplifyICond hyp prop = case evalICond prop of
    IBool b -> return $ IBool b
    IAnd i -> return $ fromHyp hyp i
    _ -> genTcError noloc $ text "Unexpected canonical form"

isValid :: (VarsIdTcM loc m,Location loc) => loc -> ICond -> TcM loc m ()
isValid l c = validIConds l [c]

validIConds :: (VarsIdTcM loc m,Location loc) => loc -> [ICond] -> TcM loc m ()
validIConds l c = do
    hyp <- solveHypotheses l
    addErrorM l (TypecheckerError (locpos l) . SMTException (pp $ IAnd hyp) (pp $ IAnd c)) $ do
        ci <- simplifyICond hyp (IAnd c)
        case ci of
            IBool b -> unless b $ genTcError (locpos l) $ text "false"
            r -> checkAny (\cfg -> checkValiditySBV l cfg (IAnd hyp) r)

-- * SBV interface

compareSBV :: (VarsIdTcM loc m,Location loc) => SMTConfig -> loc -> [ICond] -> ICond -> ICond -> TcM loc m Ordering
compareSBV cfg l hyp c1 c2 = addErrorM l (TypecheckerError (locpos l) . (ComparisonException "index condition") (pp c1) (pp c2) . Just) $ do
    let str1 = ppr (IAnd $ c1 : hyp) ++ " => " ++ ppr c2
    let str2 = ppr (IAnd $ c2 : hyp) ++ " => " ++ ppr c1
    lt <- tryValiditySBV l cfg str1 $ do
        hyp2SBV l $ IAnd $ c1 : hyp
        cond2SBV l c2
    nlt <- tryValiditySBV l cfg str1 $ do
        hyp2SBV l $ IAnd hyp
        cond2SBV l $ INot $ c1 `implies` c2
    gt <- tryValiditySBV l cfg str2 $ do
        hyp2SBV l $ IAnd $ c2 : hyp
        cond2SBV l c1
    ngt <- tryValiditySBV l cfg str1 $ do
        hyp2SBV l $ IAnd hyp
        cond2SBV l $ INot $ c2 `implies` c1
    case (lt,nlt,gt,ngt) of
        (Nothing,_,Nothing,_) -> return EQ
        (Nothing,_,_,Nothing) -> return LT
        (_,Nothing,Nothing,_) -> return GT
        otherwise -> genTcError (locpos l) $ text "not comparable"

equalSBV :: (VarsIdTcM loc m,Location loc) => SMTConfig -> loc -> [ICond] -> ICond -> ICond -> TcM loc m Bool
equalSBV cfg l hyp c1 c2 = addErrorM l (TypecheckerError (locpos l) . (EqualityException "index condition") (pp c1) (pp c2) . Just) $ do
    let str = show (pp c1 <+> text "==" <+> pp c2)
    mb <- tryValiditySBV l cfg str $ do
        hyp2SBV l $ IAnd hyp
        s1 <- cond2SBV l c1
        s2 <- cond2SBV l c2
        return (s1 .== s2)
    case mb of
        Nothing -> return True
        Just err -> throwError err

checkValiditySBV :: (VarsIdTcM loc m,Location loc) => loc -> SMTConfig -> ICond -> ICond -> TcM loc m ()
checkValiditySBV l cfg hyp prop = do
    d1 <- ppM l hyp
    d2 <- ppM l prop
    let str = d1 <+> text " => " <+> d2
    r <- validitySBV l cfg (show str) $ do
        hyp2SBV l hyp
        cond2SBV l prop
    return r

tryValiditySBV :: (MonadIO m,Location loc) => loc -> SMTConfig -> String -> TcSBV loc SBool -> TcM loc m (Maybe SecrecError)
tryValiditySBV l cfg msg prop = (validitySBV l cfg msg prop >> return Nothing) `catchError` (return . Just)

validitySBV :: (MonadIO m,Location loc) => loc -> SMTConfig -> String -> TcSBV loc SBool -> TcM loc m ()
validitySBV l cfg str sprop = do
    opts <- TcM $ State.lift Reader.ask
    when (debugTypechecker opts) $
        liftIO $ hPutStr stderr (ppr (locpos l) ++ ": Calling external SMT solver " ++ show cfg ++ " to check " ++ str ++ " ... ")
--  smt <- compileToSMTLib True False sprop
--  liftIO $ putStrLn smt
    r <- proveWithTcSBV cfg sprop
    case r of
        ThmResult (Unsatisfiable _) -> do
            when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr "ok"
        ThmResult (Satisfiable _ _) -> do
            when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr "falsifiable"
            genTcError (UnhelpfulPos $ show cfg) $ text $ show r
        otherwise -> do
            when (debugTypechecker opts) $ liftIO $ hPutStrLn stderr "error"
            genTcError (UnhelpfulPos $ show cfg) $ text $ show r

-- * Generic interface

supportedSolvers :: [SMTConfig]
supportedSolvers = map (defaultSolverConfig) [minBound..maxBound::Solver]

checkWithAny :: (MonadIO m,Location loc) => [String] -> [SecrecError] -> [SMTConfig] -> (SMTConfig -> TcM loc m a) -> TcM loc m (Either a [SecrecError])
checkWithAny names errs [] check = return $ Right errs
checkWithAny names errs (solver:solvers) check = do
    liftM Left (check solver) `catchError` \err -> do
        checkWithAny names (errs++[err]) solvers check

checkAny :: (MonadIO m,Location loc) => (SMTConfig -> TcM loc m a) -> TcM loc m a
checkAny check = do
    solvers <- liftIO sbvAvailableSolvers
    when (null solvers) $ genTcError noloc $ text "No solver found"
    res <- checkWithAny (map show solvers) [] solvers check
    case res of
        Left x -> return x
        Right errs -> throwError $ MultipleErrors errs

