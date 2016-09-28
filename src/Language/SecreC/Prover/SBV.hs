{-# LANGUAGE FlexibleInstances, ViewPatterns, RankNTypes, ConstraintKinds, DeriveDataTypeable, GADTs, ScopedTypeVariables, TypeFamilies, MultiParamTypeClasses, DoAndIfThenElse, FlexibleContexts #-}

module Language.SecreC.Prover.SBV where

import Data.SBV hiding ((<+>))
import qualified Data.SBV as SBV

import Data.Generics
import Data.IORef
import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map

import Control.Monad.State as State
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer
import Control.Monad.Trans.Control
import Control.Monad.Except
import Control.Monad.Base
import Control.Monad.Catch as Catch

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint hiding (proveWith)
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Vars
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Prover.Base
import Language.SecreC.Prover.Expression

import Text.PrettyPrint

import System.IO

hyp2SBV :: SMTK loc => loc -> IExpr -> TcSBV ()
hyp2SBV l c = do
    (inHyp,_) <- State.get
    State.modify $ \(_,st) -> (True,st)
    SBool h <- iExpr2SBV l c
    State.modify $ \(_,st) -> (inHyp,st)
    lift $ lift $ constrain h

proveWithTcSBV :: (MonadIO m) => SMTConfig -> TcSBV SBool -> TcM m ThmResult
proveWithTcSBV cfg m = proveWithTcM cfg $ evalStateT m (False,Map.empty)

proveWithTcM :: (MonadIO m) => SMTConfig -> TcM Symbolic SBool -> TcM m ThmResult
proveWithTcM cfg m = do
    arr <- Reader.ask
    env <- State.get
    st <- liftIO $ newIORef (error "proveWithTcM")
    opts <- TcM $ lift Reader.ask
    let sym = do
        e <- runSecrecMWith opts $ execTcM m arr env
        case e of
            Left err -> do
                liftIO $ writeIORef st $ Left err
                return false
            Right ((b,env'),warns) -> do
                liftIO $ writeIORef st $ Right (env',warns)
                return b
    res <- liftIO $ proveWith cfg sym
    e <- liftIO $ readIORef st
    case e of
        Left err -> do
            throwError err
        Right (env',warns) -> do
            State.put env'
            TcM $ lift $ tell warns
    return res


type TcSBV = StateT (Bool,SBVals) (TcM Symbolic)
type SBVals = Map VarIdentifier SBVal
data SBVal where
    SBool :: SBool -> SBVal
    SInt8 :: SInt8 -> SBVal
    SInt16 :: SInt16 -> SBVal
    SInt32 :: SInt32 -> SBVal
    SInt64 :: SInt64 -> SBVal
    SUint8 :: SWord8 -> SBVal
    SUint16 :: SWord16 -> SBVal
    SUint32 :: SWord32 -> SBVal
    SUint64 :: SWord64 -> SBVal
    SFloat32 :: SFloat -> SBVal
    SFloat64 :: SDouble -> SBVal
  deriving (Show)

instance Monad m => PP m SBVal where
    pp = return . text . show

iLit2SBV :: ILit -> TcSBV SBVal
iLit2SBV (IInt8 i) = return $ SInt8 $ fromIntegral i
iLit2SBV (IInt16 i) = return $ SInt16 $ fromIntegral i
iLit2SBV (IInt32 i) = return $ SInt32 $ fromIntegral i
iLit2SBV (IInt64 i) = return $ SInt64 $ fromIntegral i
iLit2SBV (IUint8 i) = return $ SUint8 $ fromIntegral i
iLit2SBV (IUint16 i) = return $ SUint16 $ fromIntegral i
iLit2SBV (IUint32 i) = return $ SUint32 $ fromIntegral i
iLit2SBV (IUint64 i) = return $ SUint64 $ fromIntegral i
iLit2SBV (IFloat32 i) = return $ SFloat32 $ realToFrac i
iLit2SBV (IFloat64 i) = return $ SFloat64 $ realToFrac i
iLit2SBV (IBool b) = return $ SBool $ fromBool b

iExpr2SBV :: SMTK loc => loc -> IExpr -> TcSBV SBVal
iExpr2SBV l (ILit lit) = iLit2SBV lit
iExpr2SBV l (IIdx v@(VarName _ (VIden n@(nonTok -> True)))) = tryResolveIExprVar (locpos l) v
iExpr2SBV l (IBinOp o e1 e2) = do
    e1' <- iExpr2SBV l e1
    e2' <- iExpr2SBV l e2
    iBinOp2SBV l o e1' e2'
iExpr2SBV l (IUnOp o e1) = do
    e1' <- iExpr2SBV l e1
    iUnOp2SBV l o e1'
iExpr2SBV l (ICond c e1 e2) = do
    SBool vc <- iExpr2SBV l c
    v1 <- iExpr2SBV l e1
    v2 <- iExpr2SBV l e2
    return $ mergeSBVal (ite vc) v1 v2
iExpr2SBV l (ISize e) = lift $ genTcError (locpos l) $ text "array size not defined in SBV"
iExpr2SBV l e = lift $ do
    ppe <- pp e
    genTcError (locpos l) $ text "iExpr2SBV:" <+> ppe

iBinOp2SBV :: SMTK loc => loc -> IBOp -> SBVal -> SBVal -> TcSBV SBVal
iBinOp2SBV l IAnd (SBool b1) (SBool b2) = return $ SBool $ b1 &&& b2
iBinOp2SBV l IOr (SBool b1) (SBool b2) = return $ SBool $ b1 ||| b2
iBinOp2SBV l IImplies (SBool b1) (SBool b2) = return $ SBool $ b1 ==> b2
iBinOp2SBV l IXor (SBool b1) (SBool b2) = return $ SBool $ b1 SBV.<+> b2
iBinOp2SBV l ILeq e1 e2 = return $ SBool $ ordSBVal (.<=) e1 e2
iBinOp2SBV l ILt e1 e2 = return $ SBool $ ordSBVal (.<) e1 e2
iBinOp2SBV l IGeq e1 e2 = return $ SBool $ ordSBVal (.>=) e1 e2
iBinOp2SBV l IGt e1 e2 = return $ SBool $ ordSBVal (.>) e1 e2
iBinOp2SBV l IEq e1 e2 = return $ SBool $ ordSBVal (.==) e1 e2
iBinOp2SBV l INeq e1 e2 = return $ SBool $ ordSBVal (./=) e1 e2
iBinOp2SBV l IPlus e1 e2 = return $ numSBVal (+) e1 e2
iBinOp2SBV l IMinus e1 e2 = return $ numSBVal (-) e1 e2
iBinOp2SBV l ITimes e1 e2 = return $ numSBVal (*) e1 e2
iBinOp2SBV l IDiv e1 e2 = return $ divisibleSBVal sDiv e1 e2
iBinOp2SBV l IMod e1 e2 = return $ divisibleSBVal sMod e1 e2
iBinOp2SBV l op e1 e2 = lift $ do
    ppop <- pp op
    genTcError (locpos l) $ text "iBinOp2SBV: unsupported op" <+> ppop

iUnOp2SBV :: SMTK loc => loc -> IUOp -> SBVal -> TcSBV SBVal
iUnOp2SBV l INot (SBool b) = return $ SBool $ bnot b
iUnOp2SBV l INeg x = return $ numSBVal (\x y -> - x) x (error "iUnOp2SBV")

mergeSBVal :: (forall a . Mergeable a => a -> a -> a) -> SBVal -> SBVal -> SBVal
mergeSBVal f (SInt8 i1) (SInt8 i2) = SInt8 $ f i1 i2
mergeSBVal f (SInt16 i1) (SInt16 i2) = SInt16 $ f i1 i2
mergeSBVal f (SInt32 i1) (SInt32 i2) = SInt32 $ f i1 i2
mergeSBVal f (SInt64 i1) (SInt64 i2) = SInt64 $ f i1 i2
mergeSBVal f (SUint8 i1) (SUint8 i2) = SUint8 $ f i1 i2
mergeSBVal f (SUint16 i1) (SUint16 i2) = SUint16 $ f i1 i2
mergeSBVal f (SUint32 i1) (SUint32 i2) = SUint32 $ f i1 i2
mergeSBVal f (SUint64 i1) (SUint64 i2) = SUint64 $ f i1 i2
mergeSBVal f (SFloat32 i1) (SFloat32 i2) = SFloat32 $ f i1 i2
mergeSBVal f (SFloat64 i1) (SFloat64 i2) = SFloat64 $ f i1 i2
mergeSBVal f (SBool i1) (SBool i2) = SBool $ f i1 i2

ordSBVal :: (forall a . OrdSymbolic a => a -> a -> SBool) -> SBVal -> SBVal -> SBool
ordSBVal f (SInt8 i1)    (SInt8 i2)    = f i1 i2
ordSBVal f (SInt16 i1)   (SInt16 i2)   = f i1 i2
ordSBVal f (SInt32 i1)   (SInt32 i2)   = f i1 i2
ordSBVal f (SInt64 i1)   (SInt64 i2)   = f i1 i2
ordSBVal f (SUint8 i1)   (SUint8 i2)   = f i1 i2
ordSBVal f (SUint16 i1)  (SUint16 i2)  = f i1 i2
ordSBVal f (SUint32 i1)  (SUint32 i2)  = f i1 i2
ordSBVal f (SUint64 i1)  (SUint64 i2)  = f i1 i2
ordSBVal f (SFloat32 i1) (SFloat32 i2) = f i1 i2
ordSBVal f (SFloat64 i1) (SFloat64 i2) = f i1 i2
ordSBVal f (SBool i1)    (SBool i2)    = f i1 i2

numSBVal :: (forall a . Num a => a -> a -> a) -> SBVal -> SBVal -> SBVal
numSBVal f (SInt8 i1) (SInt8 i2) = SInt8 $ f i1 i2
numSBVal f (SInt16 i1) (SInt16 i2) = SInt16 $ f i1 i2
numSBVal f (SInt32 i1) (SInt32 i2) = SInt32 $ f i1 i2
numSBVal f (SInt64 i1) (SInt64 i2) = SInt64 $ f i1 i2
numSBVal f (SUint8 i1) (SUint8 i2) = SUint8 $ f i1 i2
numSBVal f (SUint16 i1) (SUint16 i2) = SUint16 $ f i1 i2
numSBVal f (SUint32 i1) (SUint32 i2) = SUint32 $ f i1 i2
numSBVal f (SUint64 i1) (SUint64 i2) = SUint64 $ f i1 i2
numSBVal f (SFloat32 i1) (SFloat32 i2) = SFloat32 $ f i1 i2
numSBVal f (SFloat64 i1) (SFloat64 i2) = SFloat64 $ f i1 i2

divisibleSBVal :: (forall a . SDivisible a => a -> a -> a) -> SBVal -> SBVal -> SBVal
divisibleSBVal f (SInt8 i1) (SInt8 i2) = SInt8 $ f i1 i2
divisibleSBVal f (SInt16 i1) (SInt16 i2) = SInt16 $ f i1 i2
divisibleSBVal f (SInt32 i1) (SInt32 i2) = SInt32 $ f i1 i2
divisibleSBVal f (SInt64 i1) (SInt64 i2) = SInt64 $ f i1 i2
divisibleSBVal f (SUint8 i1) (SUint8 i2) = SUint8 $ f i1 i2
divisibleSBVal f (SUint16 i1) (SUint16 i2) = SUint16 $ f i1 i2
divisibleSBVal f (SUint32 i1) (SUint32 i2) = SUint32 $ f i1 i2
divisibleSBVal f (SUint64 i1) (SUint64 i2) = SUint64 $ f i1 i2

sbVal :: String -> Type -> Symbolic SBVal
sbVal v (BaseT (TyPrim (DatatypeBool      _))) = liftM SBool $ sBool v
sbVal v (BaseT (TyPrim (DatatypeInt8      _))) = liftM SInt8 $ sInt8 v
sbVal v (BaseT (TyPrim (DatatypeUint8     _))) = liftM SUint8 $ sWord8 v
sbVal v (BaseT (TyPrim (DatatypeInt16     _))) = liftM SInt16 $ sInt16 v
sbVal v (BaseT (TyPrim (DatatypeUint16    _))) = liftM SUint16 $ sWord16 v
sbVal v (BaseT (TyPrim (DatatypeInt32     _))) = liftM SInt32 $ sInt32 v
sbVal v (BaseT (TyPrim (DatatypeUint32    _))) = liftM SUint32 $ sWord32 v
sbVal v (BaseT (TyPrim (DatatypeInt64     _))) = liftM SInt64 $ sInt64 v
sbVal v (BaseT (TyPrim (DatatypeUint64    _))) = liftM SUint64 $ sWord64 v
sbVal v (BaseT (TyPrim (DatatypeXorUint8  _))) = liftM SUint8 $ sWord8 v
sbVal v (BaseT (TyPrim (DatatypeXorUint16 _))) = liftM SUint16 $ sWord16 v
sbVal v (BaseT (TyPrim (DatatypeXorUint32 _))) = liftM SUint32 $ sWord32 v
sbVal v (BaseT (TyPrim (DatatypeXorUint64 _))) = liftM SUint64 $ sWord64 v
sbVal v (BaseT (TyPrim (DatatypeFloat32   _))) = liftM SFloat32 $ sFloat v
sbVal v (BaseT (TyPrim (DatatypeFloat64   _))) = liftM SFloat64 $ sDouble v

tryResolveIExprVar :: Position -> Var -> TcSBV SBVal
tryResolveIExprVar l v@(VarName t (VIden n@(nonTok -> True))) = do
    mb <- lift $ tryResolveEVar l n t
    case mb of
        Just e -> lift (expr2IExpr e) >>= iExpr2SBV l
        Nothing -> do
            (inHyp,sbvs) <- State.get
            case Map.lookup n sbvs of
                Just i -> return i
                Nothing -> do
                    unless inHyp $ do
                        ppn <- lift $ pp n
                        lift $ tcError (locpos l) $ Halt $ UnresolvedVariable (ppn)
                    i <- do
                        ppv <- lift $ ppr v
                        lift $ lift $ sbVal (ppv) t
                    State.modify $ \(inHyp,sbvs) -> (inHyp,Map.insert n i sbvs)
                    return i
