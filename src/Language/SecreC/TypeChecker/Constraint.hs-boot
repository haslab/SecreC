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

solveHypotheses :: (ProverK loc m) => loc -> TcM loc m [IExpr]

tcTopCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM loc m ()

proveWith :: (ProverK loc m) => loc -> String -> TcM loc m a -> TcM loc m (Either SecrecError (a,TDict loc))

prove :: (ProverK loc m) => loc -> String -> TcM loc m a -> TcM loc m a

tcProve :: (ProverK loc m) => loc -> String -> TcM loc m a -> TcM loc m (a,TDict loc)

checkCstrM :: (ProverK loc m) => loc -> Set (Loc loc IOCstr) -> CheckCstr -> TcM loc m ()

tryResolveEVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> TcM loc m (Maybe (SExpr VarIdentifier (Typed loc)))

compares :: (ProverK loc m) => loc -> Type -> Type -> TcM loc m (Comparison (TcM loc m))

comparesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM loc m (Comparison (TcM loc m))

constraintList :: (ProverK loc m,VarsId (TcM loc m) [a],VarsId (TcM loc m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM loc m x) -> loc -> [a] -> [b] -> TcM loc m [x]

data Comparison m where
    Comparison :: VarsId m a => a -> a -> Ordering -> Comparison m
  deriving (Typeable)

compOrdering :: Comparison m -> Ordering

appendComparison :: (ProverK loc m) => loc -> Comparison (TcM loc m) -> Comparison (TcM loc m) -> TcM loc m (Comparison (TcM loc m))

appendComparisons :: (ProverK loc m) => loc -> [Comparison (TcM loc m)] -> TcM loc m (Comparison (TcM loc m))

constraintError :: (VarsIdTcM loc m,VarsId (TcM loc m) a,VarsId (TcM loc m) b,Location loc) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> Doc) -> b -> (b -> Doc) -> Maybe SecrecError -> TcM loc m res

unifiesSCond :: (ProverK loc m) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM loc m ()

unifiesSizes :: (ProverK loc m) => loc -> [(Expression VarIdentifier Type,IsVariadic)] -> [(Expression VarIdentifier Type,IsVariadic)] -> TcM loc m ()

tryCstrBool :: (ProverK loc m) => loc -> TcM loc m a -> TcM loc m Bool

tryCstrMaybe :: (ProverK loc m) => loc -> TcM loc m a -> TcM loc m (Maybe a)

comparesExpr :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m (Comparison (TcM loc m))

unifiesExpr :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m ()

unifiesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM loc m ()

isTyOf :: (ProverK loc m) => loc -> Type -> Type -> TcM loc m Bool

tcCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM loc m ()

resolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM loc m Type

tryResolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM loc m (Maybe Type)

solve :: (ProverK loc m) => loc -> TcM loc m ()

resolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM loc m ComplexType

resolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM loc m DecType

unifiesTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM loc m ()

tcTopPDecCstrM :: (ProverK loc m) => loc -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(Expression VarIdentifier Type,IsVariadic)] -> Type -> TcM loc m (DecType,[(Expression VarIdentifier Type,IsVariadic)])

expandVariadicExpr :: (ProverK loc m) => loc -> (SExpr VarIdentifier Type,IsVariadic) -> TcM loc m [SExpr VarIdentifier Type]

expandVariadicType :: (ProverK loc m) => loc -> (Type,IsVariadic) -> TcM loc m [Type]

resolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM loc m BaseType

unifiesExprTy :: (ProverK loc m) => loc -> SExpr VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()