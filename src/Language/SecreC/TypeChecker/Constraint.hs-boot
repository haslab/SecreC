{-# LANGUAGE FlexibleContexts #-}

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

solveHypotheses :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m [ICond]

tcTopCstrM :: (MonadIO m,Location loc) => loc -> TcCstr -> TcM loc m ()

proveWith :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> TcM loc m a -> TcM loc m (Either SecrecError (a,TDict loc))

prove :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> TcM loc m a -> TcM loc m a

tcProve :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> TcM loc m a -> TcM loc m (a,TDict loc)

compares :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m Ordering

checkCstrM :: (MonadIO m,Location loc) => loc -> CheckCstr -> TcM loc m ()

coercesE :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Type -> Type -> TcM loc m (Expression VarIdentifier Type)

comparesList :: (VarsIdTcM loc m,Location loc) => loc -> [Type] -> [Type] -> TcM loc m Ordering

comparesSCond :: (VarsIdTcM loc m,Location loc) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM loc m Ordering

constraintList :: (VarsIdTcM loc m,Location loc,VarsId (TcM loc m) [a],VarsId (TcM loc m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM loc m x) -> loc -> [a] -> [b] -> TcM loc m [x]

unifies :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m ()

unifiesSizes :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc m ()

equals :: (VarsIdTcM loc m,Location loc) => loc -> Type -> Type -> TcM loc m ()

unifiesList :: (VarsIdTcM loc m,Location loc) => loc -> [Type] -> [Type] -> TcM loc m ()

equalsExpr :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m ()

tcCstrM :: (MonadIO m,Location loc) => loc -> TcCstr -> TcM loc m ()

resolveTVar :: (MonadIO m,Location loc) => loc -> VarIdentifier -> TcM loc m Type

tryResolveTVar :: (MonadIO m,Location loc) => loc -> VarIdentifier -> TcM loc m (Maybe Type)

solve :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> TcM loc m ()

unifiesExpr :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc m ()

resolveCVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m ComplexType

resolveDVar :: (VarsIdTcM loc m,Location loc) => loc -> VarIdentifier -> TcM loc m DecType

unifiesTIdentifier :: (VarsIdTcM loc m,Location loc) => loc -> TIdentifier -> TIdentifier -> TcM loc m ()

tcTopPDecCstrM :: (MonadIO m,Location loc) => loc -> Bool -> PIdentifier -> (Maybe [Type]) -> [Expression VarIdentifier Type] -> Type -> TcM loc m (DecType,[Expression VarIdentifier Type])

tcTopCoerces2CstrM :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Type -> Expression VarIdentifier Type -> Type -> VarName VarIdentifier Type -> VarName VarIdentifier Type -> Type -> TcM loc m ()

tcTopCoercesCstrM :: (VarsIdTcM loc m,Location loc) => loc -> Expression VarIdentifier Type -> Type -> VarName VarIdentifier Type -> Type -> TcM loc m ()

