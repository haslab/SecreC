module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Syntax
import Language.SecreC.Error

import Text.PrettyPrint

import Data.Data

prove :: TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))

coercesError :: Location loc => loc -> Type -> Type -> TcM loc a

compares :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc Ordering

comparesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc Ordering

unifies :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()

unifiesSizes :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()

unifiesList :: (Vars loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()

equalsExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

tcCstrM :: Location loc => loc -> TCstr -> TcM loc Type

resolveTCstr :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type

resolveTVar :: Location loc => loc -> VarName VarIdentifier Type -> TcM loc Type

tryResolveTVar :: Location loc => loc -> VarName VarIdentifier Type -> TcM loc (Maybe Type)

resolveTK :: (Vars loc,Location loc) => loc -> TCstr -> TcM loc Type

solveWith :: (Vars loc,Location loc) =>  TDict loc -> TcM loc ()

solve :: (Vars loc,Location loc) => TcM loc ()

provesTVar :: Location loc => TcM loc b -> (loc -> Type -> Type -> TcM loc b) -> loc -> VarName VarIdentifier Type -> Type -> TcM loc b

unifiesExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()

constraintError :: Location loc => (Doc -> Doc -> Doc -> TypecheckerErr) -> loc -> Doc -> Doc -> TcM loc a
