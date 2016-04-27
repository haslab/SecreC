{-# LANGUAGE GADTs, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Position
import Language.SecreC.Prover.Base
import {-# SOURCE #-} Language.SecreC.Prover.Expression

import Text.PrettyPrint

import Control.Monad.IO.Class

import Data.Data
import Data.Set

solveHypotheses :: (ProverK loc m) => loc -> TcM m [IExpr]

tcTopCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM m ()

proveWith :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (Either SecrecError (a,TDict Position))

prove :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a

tcProve :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict Position)

checkCstrM :: (ProverK loc m) => loc -> Set (Loc Position IOCstr) -> CheckCstr -> TcM m ()

tryResolveEVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> TcM m (Maybe (SExpr VarIdentifier (Typed loc)))

compares :: (ProverK loc m) => loc -> Type -> Type -> TcM m (Comparison (TcM m))

comparesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m (Comparison (TcM m))

constraintList :: (ProverK loc m,VarsId (TcM m) [a],VarsId (TcM m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM m x) -> loc -> [a] -> [b] -> TcM m [x]

data Comparison m where
    Comparison :: VarsId m a => a -> a -> Ordering -> Comparison m
  deriving (Typeable)

compOrdering :: Comparison m -> Ordering

appendComparison :: (ProverK loc m) => loc -> Comparison (TcM m) -> Comparison (TcM m) -> TcM m (Comparison (TcM m))

appendComparisons :: (ProverK loc m) => loc -> [Comparison (TcM m)] -> TcM m (Comparison (TcM m))

constraintError :: (Typeable loc,VarsIdTcM m,VarsId (TcM m) a,VarsId (TcM m) b,Location loc) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> Doc) -> b -> (b -> Doc) -> Maybe SecrecError -> TcM m res

unifiesSCond :: (ProverK loc m) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM m ()

unifiesSizes :: (ProverK loc m) => loc -> [(Expression VarIdentifier Type,IsVariadic)] -> [(Expression VarIdentifier Type,IsVariadic)] -> TcM m ()

tryCstrBool :: (ProverK loc m) => loc -> TcM m a -> TcM m Bool

tryCstrMaybe :: (ProverK loc m) => loc -> TcM m a -> TcM m (Maybe a)

comparesExpr :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Comparison (TcM m))

unifiesExpr :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m ()

unifiesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()

isTyOf :: (ProverK loc m) => loc -> Type -> Type -> TcM m Bool

tcCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM m ()

resolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m Type

tryResolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe Type)

solve :: (ProverK loc m) => loc -> TcM m ()

resolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m ComplexType

resolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m DecType

unifiesTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()

tcTopPDecCstrM :: (ProverK loc m) => loc -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(Expression VarIdentifier Type,IsVariadic)] -> Type -> TcM m (DecType,[(Expression VarIdentifier Type,IsVariadic)])

expandVariadicExpr :: (ProverK loc m) => loc -> (SExpr VarIdentifier Type,IsVariadic) -> TcM m [SExpr VarIdentifier Type]

expandVariadicType :: (ProverK loc m) => loc -> (Type,IsVariadic) -> TcM m [Type]

resolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m BaseType

unifiesExprTy :: (ProverK loc m) => loc -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM m ()