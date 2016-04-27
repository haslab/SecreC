{-# LANGUAGE TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, ConstraintKinds, DeriveGeneric, DeriveDataTypeable #-}

module Language.SecreC.Prover.Base where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Syntax
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.Location
import {-# SOURCE #-} Language.SecreC.Transformation.Simplify
import Language.SecreC.Vars

import Data.Hashable
import Data.Typeable
import Data.Data
import Data.Int
import Data.Word
import Data.SBV hiding ((<+>))

import Control.Monad.IO.Class
import Control.Monad.Base
import Control.Monad.Trans.Control
import Control.Monad

import Text.PrettyPrint

import GHC.Generics

data ILit
    = IInt8 Int8
    | IInt16 Int16
    | IInt32 Int32
    | IInt64 Int64
    | IUint8 Word8
    | IUint16 Word16 
    | IUint32 Word32 
    | IUint64 Word64 
    | IFloat32 Float 
    | IFloat64 Double
    | IBool Bool
  deriving (Eq, Ord, Show, Data, Typeable,Generic)
instance Hashable ILit
instance PP ILit where
    pp (IInt8 i) = text (show i)
    pp (IInt16 i) = text (show i)
    pp (IInt32 i) = text (show i)
    pp (IInt64 i) = text (show i)
    pp (IUint8 i) = text (show i)
    pp (IUint16 i) = text (show i)
    pp (IUint32 i) = text (show i)
    pp (IUint64 i) = text (show i)
    pp (IFloat32 i) = text (show i)
    pp (IFloat64 i) = text (show i)
    pp (IBool True) = text "true"
    pp (IBool False) = text "false"

data IExpr
    = ILit ILit -- index literal
    | IIdx (VarName VarIdentifier Type) -- index variable
    | IBinOp IBOp IExpr IExpr
    | IUnOp IUOp IExpr
    | ICond IExpr IExpr IExpr -- conditional
    | ISize IExpr -- array size (dimension,array expression)
    | IArr ComplexType [[IExpr]] -- multi-dimensional array value
  deriving (Eq, Ord, Show, Data, Typeable,Generic)
instance Hashable IExpr
instance PP IExpr where
    pp (ILit l) = pp l
    pp (IIdx v) = pp v
    pp (IBinOp o e1 e2) = parens (pp e1 <+> pp o <+> pp e2)
    pp (IUnOp o e1) = parens (pp o <+> pp e1)
    pp (ICond c e1 e2) = pp c <> char '?' <> pp e1 <> char ':' <> pp e2
    pp (ISize e) = text "size" <> parens (pp e)
    pp (IArr t vvs) = braces (sepBy comma $ map (\vs -> sepBy comma $ map pp vs) vvs) <> text "::" <> pp t

data IBOp
    = IAnd -- boolean conjunction
    | IOr -- boolean disjunction
    | IXor -- ^ Boolean exclusive disjunction
    | IImplies -- boolean implication
    | ILeq -- less or equal than
    | ILt -- less than
    | IGeq -- greater or equal than
    | IGt -- greater than
    | IEq -- equal
    | INeq -- not equal
    | IPlus -- ^ Addition
    | IMinus -- ^ Substraction
    | ITimes -- ^ Multiplication
    | IPower -- ^ Exponentiation
    | IDiv -- ^ Whole division
    | IMod -- ^ Remainer of whole division
  deriving (Eq, Ord, Show, Data, Typeable,Generic)
instance Hashable IBOp
instance PP IBOp where
    pp IAnd = text "&&"
    pp IOr = text "||"
    pp IXor = text "^^"
    pp IImplies = text "==>"
    pp (ILeq) = text "<="
    pp (IEq) = text "=="
    pp (INeq) = text "!="
    pp (IPlus) = text "+"
    pp (IMinus) = text "-"
    pp (IPower) = text "**"
    pp (IDiv) = text "/"
    pp (IMod) = text "%"
    pp ILt = text "<"
    pp IGeq = text ">="
    pp IGt = text ">"

data IUOp
    = INot -- boolean negation
    | INeg -- integer negation
  deriving (Eq, Ord, Show, Data, Typeable,Generic)
instance Hashable IUOp
instance PP IUOp where
    pp INot = text "!"
    pp INeg = text "-"

iAnd :: [IExpr] -> IExpr
iAnd [] = ILit (IBool True)
iAnd xs = foldl1 (IBinOp IAnd) xs

iExprTy :: IExpr -> Type
iExprTy (ILit lit) = iLitTy lit
iExprTy (IIdx v) = loc v
iExprTy (IBinOp IAnd e1 e2) = BaseT bool
iExprTy (IBinOp IOr e1 e2) = BaseT bool
iExprTy (IBinOp IXor e1 e2) = BaseT bool
iExprTy (IBinOp ILeq e1 e2) = BaseT bool
iExprTy (IBinOp IEq e1 e2) = BaseT bool
iExprTy (IBinOp INeq e1 e2) = BaseT bool
iExprTy (IBinOp IPlus e1 e2) = iExprTy e1
iExprTy (IBinOp IMinus e1 e2) = iExprTy e1
iExprTy (IBinOp IPower e1 e2) = iExprTy e1
iExprTy (IBinOp IDiv e1 e2) = iExprTy e1
iExprTy (IBinOp IMod e1 e2) = iExprTy e1
iExprTy (IUnOp INot e) = BaseT bool
iExprTy (IUnOp INeg e) = iExprTy e
iExprTy (ICond _ e1 e2) = iExprTy e1
iExprTy (ISize e) = BaseT index
iExprTy (IArr t vvs) = ComplexT t

iLitTy :: ILit -> Type
iLitTy (IInt8 _) = BaseT $ TyPrim $ DatatypeInt8 ()
iLitTy (IInt16 _) = BaseT $ TyPrim $ DatatypeInt16 ()
iLitTy (IInt32 _) = BaseT $ TyPrim $ DatatypeInt32 ()
iLitTy (IInt64 _) = BaseT $ TyPrim $ DatatypeInt64 ()
iLitTy (IUint8 _) = BaseT $ TyPrim $ DatatypeUint8 ()
iLitTy (IUint16 _) = BaseT $ TyPrim $ DatatypeUint16 ()
iLitTy (IUint32 _) = BaseT $ TyPrim $ DatatypeUint32 ()
iLitTy (IUint64 _) = BaseT $ TyPrim $ DatatypeUint64 ()
iLitTy (IFloat32 _) = BaseT $ TyPrim $ DatatypeFloat32 ()
iLitTy (IFloat64 _) = BaseT $ TyPrim $ DatatypeFloat64 ()
iLitTy (IBool _) = BaseT $ TyPrim $ DatatypeBool ()

instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m ILit where
    traverseVars f (IInt8 i) = liftM IInt8 $ f i
    traverseVars f (IInt16 i) = liftM IInt16 $ f i
    traverseVars f (IInt32 i) = liftM IInt32 $ f i
    traverseVars f (IInt64 i) = liftM IInt64 $ f i
    traverseVars f (IUint8 i) = liftM IUint8 $ f i
    traverseVars f (IUint16 i) = liftM IUint16 $ f i
    traverseVars f (IUint32 i) = liftM IUint32 $ f i
    traverseVars f (IUint64 i) = liftM IUint64 $ f i
    traverseVars f (IFloat32 i) = liftM IFloat32 $ f i
    traverseVars f (IFloat64 i) = liftM IFloat64 $ f i
    traverseVars f (IBool i) = liftM IBool $ f i
instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m IExpr where
    traverseVars f (ILit i) = liftM ILit $ f i
    traverseVars f (IIdx v) = do
        v' <- f v
        return $ IIdx v'
    traverseVars f (IBinOp o e1 e2) = do
        o' <- f o
        e1' <- f e1
        e2' <- f e2
        return $ IBinOp o' e1' e2'
    traverseVars f (IUnOp o e1) = do
        o' <- f o
        e1' <- f e1
        return $ IUnOp o' e1'
    traverseVars f (ISize e) = do
        e' <- f e
        return $ ISize e'
    traverseVars f (IArr t vvs) = do
        t' <- f t
        vvs' <- mapM (mapM f) vvs
        return $ IArr t' vvs'
    substL (IIdx (VarName _ n)) = return $ Just n
    substL _ = return Nothing
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m IBOp where
    traverseVars f o = return o
instance (GenVar iden m,IsScVar iden,MonadIO m) => Vars iden m IUOp where
    traverseVars f o = return o

 

type ProverK loc m = (SMTK loc,SimplifyK loc (TcM) m,VarsIdTcM m,Location loc)
type SMTK loc = (Vars VarIdentifier Symbolic loc,VarsIdTcM Symbolic,Location loc)

instance MonadBase IO Symbolic where
    liftBase = liftIO

instance MonadBaseControl IO Symbolic where
    type StM Symbolic a = Symbolic a
    liftBaseWith f = liftIO $ f return
    restoreM       = id

instance GenVar VarIdentifier Symbolic where
    genVar v = freshVarIO v
    
