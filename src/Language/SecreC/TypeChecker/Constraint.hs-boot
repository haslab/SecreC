module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Syntax

import Data.Data

prove :: TcProofM loc a -> TcM loc (Maybe (a,Substs Type))

equals :: Location loc => loc -> Type -> Type -> TcProofM loc ()

equalsList :: Location loc => loc -> [Type] -> [Type] -> TcProofM loc ()

coerces :: Location loc => loc -> Type -> Type -> TcProofM loc ()

coerces2 :: Location loc => loc -> Type -> Type -> TcProofM loc Type

compares :: Location loc => loc -> Type -> Type -> TcProofM loc Ordering

comparesList :: Location loc => loc -> [Type] -> [Type] -> TcProofM loc Ordering

unifies :: Location loc => loc -> Type -> Type -> TcProofM loc ()

unifiesList :: Location loc => loc -> [Type] -> [Type] -> TcProofM loc ()

equalsExpr :: Location loc => loc -> Expression () -> Expression () -> TcProofM loc ()

tcCstr :: Location loc => loc -> TCstr -> TcProofM loc (Maybe Type)

tcCstrM :: Location loc => loc -> TCstr -> TcM loc Type

resolveTCstr :: Location loc => loc -> TCstr -> TcProofM loc Type