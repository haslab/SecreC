{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Syntax
import Language.SecreC.Error
import Language.SecreC.Position

import Text.PrettyPrint

import Data.Data

solveHypotheses :: (Vars (TcM loc) loc,Location loc) => TcM loc [ICond VarIdentifier]

tcTopCstrM :: Location loc => loc -> TcCstr -> TcM loc ()

proveWith :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))

prove :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc a

tcProve :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc (a,TDict loc)

compares :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc Ordering

checkCstrM :: Location loc => loc -> CheckCstr -> TcM loc ()

coercesE :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Type -> Type -> TcM loc (Expression VarIdentifier Type)

comparesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc Ordering

comparesSCond :: (VarsTcM loc,Location loc) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM loc Ordering

constraintList :: (VarsTcM loc,Location loc,Vars (TcM Position) [a],Vars (TcM Position) [b]) =>
    (Doc -> Doc -> Either Doc SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM loc x) -> loc -> [a] -> [b] -> TcM loc [x]

unifies :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc ()

unifiesSizes :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()

equals :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc ()

unifiesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()

equalsExpr :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

tcCstrM :: Location loc => loc -> TcCstr -> TcM loc ()

resolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc Type

tryResolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc (Maybe Type)

solve :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc ()

unifiesExpr :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

resolveCVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc ComplexType

resolveDVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc DecType

unifiesTIdentifier :: (VarsTcM loc,Location loc) => loc -> TIdentifier -> TIdentifier -> TcM loc ()

tcTopPDecCstrM :: Location loc => loc -> Bool -> PIdentifier -> (Maybe [Type]) -> [Expression VarIdentifier Type] -> Type -> TcM loc (DecType,[Expression VarIdentifier Type])

tcTopCoerces2CstrM :: (Vars (TcM loc) loc,Location loc) => loc -> Expression VarIdentifier Type -> Type -> Expression VarIdentifier Type -> Type -> VarName VarIdentifier Type -> VarName VarIdentifier Type -> Type -> TcM loc ()

tcTopCoercesCstrM :: (Vars (TcM loc) loc,Location loc) => loc -> Expression VarIdentifier Type -> Type -> VarName VarIdentifier Type -> Type -> TcM loc ()