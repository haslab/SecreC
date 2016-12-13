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

isZeroIdxExpr :: ProverK loc m => loc -> Expr -> TcM m (Either SecrecError Bool)

solveHypotheses :: (ProverK loc m) => loc -> TcM m [IExpr]

topTcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()

proveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m (a,TDict)

proveWithMode :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m a

prove :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a

tcProve :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict)

checkCstrM_ :: (ProverK loc m) => loc -> Set (LocIOCstr) -> CheckCstr -> TcM m ()

topCheckCstrM :: (ProverK loc m) => loc -> Set (Loc Position IOCstr) -> CheckCstr -> TcM m (Maybe IOCstr)

topCheckCstrM_ :: (ProverK loc m) => loc -> Set (Loc Position IOCstr) -> CheckCstr -> TcM m ()

tryResolveEVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> TcM m (Maybe (Expression GIdentifier (Typed loc)))

compares :: (ProverK loc m) => loc -> Bool -> Type -> Type -> TcM m (Comparison (TcM m))

equals :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()

solveTop :: ProverK loc m => loc -> String -> TcM m ()

comparesList :: (ProverK loc m) => loc -> Bool -> [Type] -> [Type] -> TcM m (Comparison (TcM m))

constraintList :: (ProverK loc m,VarsG (TcM m) [a],VarsG (TcM m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM m x) -> loc -> [a] -> [b] -> TcM m [x]

data Comparison m where
    Comparison :: VarsG m a => a -> a -> Ordering -> Ordering -> Bool -> Comparison m
  deriving (Typeable)

compOrdering :: Comparison m -> (Ordering,Ordering,Bool)

appendComparison :: (ProverK loc m) => loc -> Comparison (TcM m) -> Comparison (TcM m) -> TcM m (Comparison (TcM m))

appendComparisons :: (ProverK loc m) => loc -> [Comparison (TcM m)] -> TcM m (Comparison (TcM m))

appendOrderings :: ProverK loc m => loc -> [Ordering] -> TcM m Ordering

constraintError :: (ProverK loc m,VarsG (TcM m) a,VarsG (TcM m) b) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> TcM m Doc) -> b -> (b -> TcM m Doc) -> Maybe SecrecError -> TcM m res

tryCstrBool :: (ProverK loc m) => loc -> TcM m a -> TcM m Bool

tryCstrMaybe :: (ProverK loc m) => loc -> TcM m a -> TcM m (Maybe a)

comparesExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))

unifiesExpr :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()

unifiesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()

isTyOf :: (ProverK loc m) => loc -> Type -> Type -> TcM m Bool

expandCTypeVar :: (ProverK loc m) => loc -> VarIdentifier -> Bool -> TcM m ComplexType

assignsExprTy :: (ProverK loc m) => loc -> Var -> Expr -> TcM m ()

unifies :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()

tcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()

resolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m Type

tryResolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> Bool -> TcM m (Maybe ComplexType)

tryResolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe Type)

solve :: (ProverK loc m) => loc -> String -> TcM m ()

resolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> Bool -> TcM m ComplexType

resolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m DecType

unifiesTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()

pDecCstrM :: (ProverK loc m) => loc -> Maybe [EntryEnv] -> Bool -> Bool -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(IsConst,Either Expr Type,IsVariadic)] -> Type -> TcM m (DecType,[(IsConst,Either Expr Type,IsVariadic)])

expandVariadicExpr :: (ProverK loc m) => loc -> Bool -> (Expr,IsVariadic) -> TcM m [Expr]

expandVariadicType :: (ProverK loc m) => loc -> (Type,IsVariadic) -> TcM m [Type]

resolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> Maybe DataClass -> TcM m BaseType

resolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> KindType -> TcM m SecType

tryResolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> Maybe DataClass -> TcM m (Maybe BaseType)

tryResolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> KindType -> TcM m (Maybe SecType)

tryResolveKVar :: (ProverK loc m) => loc -> VarIdentifier -> Maybe KindClass -> TcM m (Maybe KindType)

tryResolveVAVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> Expr -> TcM m (Maybe VArrayType)

tryResolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe DecType)

unifiesKind :: ProverK loc m => loc -> KindType -> KindType -> TcM m ()

tcCoercesN :: ProverK loc m => loc -> Bool -> [Expr] -> Type -> TcM m [Expr]

unifiesExprTy :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()

unifiesSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()
equalsSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()

projectArrayExpr :: ProverK loc m => loc -> Expr -> [Index GIdentifier Type] -> TcM m Expr

tryTcError :: ProverK loc m => loc -> TcM m a -> TcM m (Either SecrecError a)

tcCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM m (Maybe IOCstr)

tcCoerces :: ProverK loc m => loc -> Bool -> Maybe [Type] -> Expr -> Type -> TcM m Expr

sizeToken :: MonadIO m => TcM m Expr