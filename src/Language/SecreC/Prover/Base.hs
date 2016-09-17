{-# LANGUAGE UndecidableInstances, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, ConstraintKinds, DeriveGeneric, DeriveDataTypeable #-}

module Language.SecreC.Prover.Base where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Syntax
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Vars
import Language.SecreC.Error

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
import Control.Monad.Except

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
    | ILitArr BaseType [[ILit]]
  deriving (Eq, Ord, Show, Data, Typeable,Generic)
instance Hashable ILit
instance Monad m => PP m ILit where
    pp (IInt8 i) =      return $ text (show i)
    pp (IInt16 i) =     return $ text (show i)
    pp (IInt32 i) =     return $ text (show i)
    pp (IInt64 i) =     return $ text (show i)
    pp (IUint8 i) =     return $ text (show i)
    pp (IUint16 i) =    return $ text (show i)
    pp (IUint32 i) =    return $ text (show i)
    pp (IUint64 i) =    return $ text (show i)
    pp (IFloat32 i) =   return $ text (show i)
    pp (IFloat64 i) =   return $ text (show i)
    pp (IBool True) =   return $ text "true"
    pp (IBool False) =  return $ text "false"
    pp (ILitArr t xs) = do
        pp1 <- mapM (liftM (braces . sepBy comma) . mapM pp) xs
        return $ braces (sepBy comma pp1)

data IExpr
    = ILit ILit -- index literal
    | IIdx Var -- index variable
    | IBinOp IBOp IExpr IExpr
    | IUnOp IUOp IExpr
    | ICond IExpr IExpr IExpr -- conditional
    | ISize IExpr -- array size (dimension,array expression)
    | IShape IExpr -- array shape
    | IArr ComplexType [[IExpr]] -- multi-dimensional array value
  deriving (Eq, Ord, Show, Data, Typeable,Generic)
instance Hashable IExpr
instance PP m VarIdentifier => PP m IExpr where
    pp (ILit l) = pp l
    pp (IIdx v) = pp v
    pp (IBinOp o e1 e2) = do
        pp1 <- pp e1
        pp2 <- pp o
        pp3 <- pp e2
        return $ parens (pp1 <+> pp2 <+> pp3)
    pp (IUnOp o e1) = do
        pp1 <- pp o
        pp2 <- pp e1
        return $ parens (pp1 <+> pp2)
    pp (ICond c e1 e2) = do
        pp1 <- pp c
        pp2 <- pp e1
        pp3 <- pp e2
        return $ pp1 <> char '?' <> pp2 <> char ':' <> pp3
    pp (ISize e) = do
        pp1 <- pp e
        return $ text "size" <> parens pp1
    pp (IShape e) = do
        pp1 <- pp e
        return $ text "shape" <> parens pp1
    pp (IArr t vvs) = do
        let f vs = liftM (sepBy comma) $ mapM pp vs
        ppf <- mapM f vvs
        ppt <- pp t
        return $ braces (sepBy comma ppf) <> text "::" <> ppt

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
instance Monad m => PP m IBOp where
    pp IAnd =     return $ text "&&"
    pp IOr =      return $ text "||"
    pp IXor =     return $ text "^^"
    pp IImplies = return $ text "==>"
    pp (ILeq) =   return $ text "<="
    pp (IEq) =    return $ text "=="
    pp (INeq) =   return $ text "!="
    pp (IPlus) =  return $ text "+"
    pp (IMinus) = return $ text "-"
    pp (IPower) = return $ text "**"
    pp (IDiv) =   return $ text "/"
    pp (IMod) =   return $ text "%"
    pp ILt =      return $ text "<"
    pp IGeq =     return $ text ">="
    pp IGt =      return $ text ">"

data IUOp
    = INot -- boolean negation
    | INeg -- integer negation
  deriving (Eq, Ord, Show, Data, Typeable,Generic)
instance Hashable IUOp
instance Monad m => PP m IUOp where
    pp INot = return $ text "!"
    pp INeg = return $ text "-"

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
iExprTy (IShape e) = ComplexT $ CType Public index (indexExpr 1)
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
iLitTy (ILitArr b xs) = ComplexT $ CType Public b (indexExpr $ fromInteger $ toInteger $ length xs)

instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m ILit where
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
    traverseVars f (ILitArr t xs) = do
        t' <- f t
        liftM (ILitArr t') $ mapM (mapM f) xs
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m IExpr where
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
    traverseVars f (IShape e) = do
        e' <- f e
        return $ IShape e'
    traverseVars f (IArr t vvs) = do
        t' <- f t
        vvs' <- mapM (mapM f) vvs
        return $ IArr t' vvs'
    substL (IIdx (VarName _ n)) = return $ Just n
    substL _ = return Nothing
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m IBOp where
    traverseVars f o = return o
instance (GenVar iden m,IsScVar m iden,MonadIO m) => Vars iden m IUOp where
    traverseVars f o = return o

type ProverK loc m = (SMTK loc,Vars VarIdentifier (TcM m) loc,VarsIdTcM m,Location loc)
type SMTK loc = (VarsIdTcM Symbolic,Location loc)
--Vars VarIdentifier Symbolic loc,

instance MonadBase IO Symbolic where
    liftBase = liftIO

instance MonadBaseControl IO Symbolic where
    type StM Symbolic a = Symbolic a
    liftBaseWith f = liftIO $ f return
    restoreM       = id

--instance GenVar VarIdentifier Symbolic where
--    genVar v = freshVarIO v
    
