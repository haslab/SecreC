{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Syntax
import Language.SecreC.Error

import Text.PrettyPrint

import Data.Data


tcTopCstrM :: Location loc => loc -> TCstr -> TcM loc Type

proveWith :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))

prove :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc a

tcProve :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc (a,TDict loc)

compares :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc Ordering

comparesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc Ordering

unifies :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc ()

unifiesSizes :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()

unifiesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()

equalsExpr :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

tcCstrM :: Location loc => loc -> TCstr -> TcM loc Type

resolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc Type

tryResolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc (Maybe Type)

solve :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc ()

coercesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()

unifiesExpr :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

resolveCVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc ComplexType

resolveDVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc DecType

unifiesTIdentifier :: (VarsTcM loc,Location loc) => loc -> TIdentifier -> TIdentifier -> TcM loc ()

