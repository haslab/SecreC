{-# LANGUAGE GADTs, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Position

import Text.PrettyPrint

import Control.Monad.IO.Class

import Data.Data
import Data.Set

solveHypotheses :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m [ICond]

tcTopCstrM :: (MonadIO m,Location loc) => loc -> TcCstr -> TcM loc m ()

proveWith :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m a -> TcM loc m (Either SecrecError (a,TDict loc))

prove :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m a -> TcM loc m a

tcProve :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m a -> TcM loc m (a,TDict loc)

checkCstrM :: (MonadIO m,Location loc) => loc -> Set (Loc loc IOCstr) -> CheckCstr -> TcM loc m ()

coercesE :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Type -> Type -> TcM loc m (Expression VarIdentifier Type)

tryResolveEVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> Type -> TcM loc m (Maybe (SExpr VarIdentifier (Typed loc)))

compares :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m (Comparison (TcM loc m))

comparesList :: (VarsIdTcM loc m,Location loc) => loc -> [Type] -> [Type] -> TcM loc m (Comparison (TcM loc m))

constraintList :: (VarsIdTcM loc m,Location loc,VarsId (TcM loc m) [a],VarsId (TcM loc m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM loc m x) -> loc -> [a] -> [b] -> TcM loc m [x]

data Comparison m where
    Comparison :: VarsId m a => a -> a -> Ordering -> Comparison m
  deriving (Typeable)

compOrdering :: Comparison m -> Ordering

appendComparison :: (VarsIdTcM loc m,Location loc) => loc -> Comparison (TcM loc m) -> Comparison (TcM loc m) -> TcM loc m (Comparison (TcM loc m))

appendComparisons :: (VarsIdTcM loc m,Location loc) => loc -> [Comparison (TcM loc m)] -> TcM loc m (Comparison (TcM loc m))

constraintError :: (VarsIdTcM loc m,VarsId (TcM loc m) a,VarsId (TcM loc m) b,Location loc) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> Doc) -> b -> (b -> Doc) -> Maybe SecrecError -> TcM loc m res

unifiesSizes :: (VarsIdTcM loc m,Location loc) => loc -> [(Expression VarIdentifier Type,IsVariadic)] -> [(Expression VarIdentifier Type,IsVariadic)] -> TcM loc m ()

tryUnifiesBool :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m Bool

unifiesList :: (VarsIdTcM loc m,Location loc) => loc -> [Type] -> [Type] -> TcM loc m ()

tCstrM :: (MonadIO m,Location loc) => loc -> TCstr -> TcM loc m IOCstr

isTyOf :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m Bool

tcCstrM :: (MonadIO m,Location loc) => loc -> TcCstr -> TcM loc m ()

tcCstrM' :: (MonadIO m,Location loc) => loc -> TcCstr -> TcM loc m IOCstr

resolveTVar :: (MonadIO m,Location loc) => loc -> VarIdentifier -> TcM loc m Type

tryResolveTVar :: (MonadIO m,Location loc) => loc -> VarIdentifier -> TcM loc m (Maybe Type)

solve :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m ()

resolveCVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m ComplexType

resolveDVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m DecType

unifiesTIdentifier :: (VarsIdTcM loc m,Location loc) => loc -> TIdentifier -> TIdentifier -> TcM loc m ()

tcTopPDecCstrM :: (MonadIO m,Location loc) => loc -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(Expression VarIdentifier Type,IsVariadic)] -> Type -> TcM loc m (DecType,[(Expression VarIdentifier Type,IsVariadic)])

expandVariadicExpr :: (VarsIdTcM loc m,Location loc) => loc -> (SExpr VarIdentifier Type,IsVariadic) -> TcM loc m [SExpr VarIdentifier Type]

expandVariadicType :: (VarsIdTcM loc m,Location loc) => loc -> (Type,IsVariadic) -> TcM loc m [Type]

resolveBVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m BaseType