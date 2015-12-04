module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Syntax
import Language.SecreC.Error

import Text.PrettyPrint

import Data.Data

tcTopCstrM :: Location loc => loc -> TCstr -> TcM loc Type

proveWith :: (Vars loc,Location loc) => TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))

prove :: (Vars loc,Location loc) => TcM loc a -> TcM loc a

compares :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Ordering

comparesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc Ordering

unifies :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()

unifiesSizes :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()

unifiesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()

equalsExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

tcCstrM :: Location loc => loc -> TCstr -> TcM loc Type

resolveTCstr :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type

resolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc Type

tryResolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc (Maybe Type)

resolveTK :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type

solve :: (Vars loc,Location loc) => TcM loc ()

coercesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()

unifiesExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

constraintError :: Location loc => (Doc -> Doc -> Either Doc SecrecError -> TypecheckerErr) -> loc -> Doc -> Doc -> Maybe SecrecError -> TcM loc a

resolveCVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc ComplexType
