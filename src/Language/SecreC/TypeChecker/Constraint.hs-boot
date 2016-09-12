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

import GHC.Generics (Generic)

import Text.PrettyPrint

import Control.Monad.IO.Class

import Data.Data
import Data.Set

isZeroIdxExpr :: ProverK loc m => loc -> Expr -> TcM m ()

solveHypotheses :: (ProverK loc m) => loc -> TcM m [IExpr]

topTcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()

proveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m (a,TDict)

proveWithMode :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m a

prove :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a

tcProve :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict)

checkCstrM_ :: (ProverK loc m) => loc -> Set (LocIOCstr) -> CheckCstr -> TcM m ()

topCheckCstrM :: (ProverK loc m) => loc -> Set (Loc Position IOCstr) -> CheckCstr -> TcM m (Maybe IOCstr)

topCheckCstrM_ :: (ProverK loc m) => loc -> Set (Loc Position IOCstr) -> CheckCstr -> TcM m ()

tryResolveEVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> TcM m (Maybe (Expression VarIdentifier (Typed loc)))

compares :: (ProverK loc m) => loc -> Bool -> Type -> Type -> TcM m (Comparison (TcM m))

equals :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()

solveTop :: ProverK loc m => loc -> String -> TcM m ()

comparesList :: (ProverK loc m) => loc -> Bool -> [Type] -> [Type] -> TcM m (Comparison (TcM m))

constraintList :: (ProverK loc m,VarsId (TcM m) [a],VarsId (TcM m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM m x) -> loc -> [a] -> [b] -> TcM m [x]

data Comparison m where
    Comparison :: VarsId m a => a -> a -> Ordering -> Ordering -> Comparison m
  deriving (Typeable)

compOrdering :: Comparison m -> (Ordering,Ordering)

appendComparison :: (ProverK loc m) => loc -> Comparison (TcM m) -> Comparison (TcM m) -> TcM m (Comparison (TcM m))

appendComparisons :: (ProverK loc m) => loc -> [Comparison (TcM m)] -> TcM m (Comparison (TcM m))

constraintError :: (ProverK loc m,VarsId (TcM m) a,VarsId (TcM m) b) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> Doc) -> b -> (b -> Doc) -> Maybe SecrecError -> TcM m res

unifiesCondExpression :: (ProverK loc m) => loc -> CondExpression VarIdentifier Type -> CondExpression VarIdentifier Type -> TcM m ()

unifiesSizes :: (ProverK loc m) => loc -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> TcM m ()

tryCstrBool :: (ProverK loc m) => loc -> TcM m a -> TcM m Bool

tryCstrMaybe :: (ProverK loc m) => loc -> TcM m a -> TcM m (Maybe a)

comparesExpr :: (ProverK loc m) => loc -> Bool -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m (Comparison (TcM m))

unifiesExpr :: (ProverK loc m) => loc -> Bool -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m ()

unifiesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()

isTyOf :: (ProverK loc m) => loc -> Type -> Type -> TcM m Bool

expandCTypeVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m ComplexType

assignsExprTy :: (ProverK loc m) => loc -> Var -> Expr -> TcM m ()

unifies :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()

tcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()

resolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m Type

tryResolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe ComplexType)

tryResolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe Type)

solve :: (ProverK loc m) => loc -> String -> TcM m ()

resolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m ComplexType

resolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m DecType

unifiesTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()

pDecCstrM :: (ProverK loc m) => loc -> Bool -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(Expr,IsVariadic)] -> Type -> TcM m (DecType,[(Expr,IsVariadic)])

expandVariadicExpr :: (ProverK loc m) => loc -> (Expression VarIdentifier Type,IsVariadic) -> TcM m [Expression VarIdentifier Type]

expandVariadicType :: (ProverK loc m) => loc -> (Type,IsVariadic) -> TcM m [Type]

resolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m BaseType

resolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m SecType

tryResolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe SecType)

unifiesKind :: ProverK loc m => loc -> KindType -> KindType -> TcM m ()

unifiesExprTy :: (ProverK loc m) => loc -> Bool -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM m ()

unifiesSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()