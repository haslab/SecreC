{-# LANGUAGE RankNTypes, DeriveDataTypeable, ViewPatterns, FlexibleContexts, GADTs #-}

-- Static semantics, used by the typechecker to evaluate indexes
module Language.SecreC.Prover.Semantics where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import {-# SOURCE #-} Language.SecreC.Prover.Expression

import Data.Int
import Data.Word
import Data.Map as Map
import Data.Maybe
import Data.List as List
import Data.Generics

import Text.PrettyPrint

import System.Timeout.Lifted

import Control.Monad
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Control.Monad.Reader as Reader
import Control.Monad.Except
import Control.Monad.Trans.Control

-- * Exports

evaluateIndexExpr :: (ProverK loc m) => loc -> Expression VarIdentifier Type -> TcM loc m Word64
evaluateIndexExpr l e = do
    IUint64 w <- evaluateExpr l $ fmap (Typed l) e
    return w

evaluateExpr :: (ProverK loc m) => loc -> Expression VarIdentifier (Typed loc) -> TcM loc m ILit
evaluateExpr l e = evaluate l (text "evaluateExpr") (evalIExpr =<< expr2IExpr e)

evaluateIExpr :: (ProverK loc m) => loc -> IExpr -> TcM loc m ILit
evaluateIExpr l e = evaluate l (text "evaluateExpr") (evalIExpr e)

---- * Internal declarations

evaluate :: (ProverK loc m) => loc -> Doc -> TcM loc m a -> TcM loc m a
evaluate l doc m = do
    arr <- Reader.ask
    env <- State.get
    opts <- TcM $ lift Reader.ask
    mb <- lift $ timeout (evalTimeOut opts * 10^6) $ runSecrecMWith opts $ execTcM m arr env
    case mb of
        Nothing -> tcError (locpos l) $ Halt $ StaticEvalError doc $ Just $ TimedOut $ evalTimeOut opts
        Just (Left err) -> tcError (locpos l) $ Halt $ StaticEvalError doc $ Just err
        Just (Right ((x,env'),warns)) -> do
            State.put env'
            TcM (lift $ Writer.tell warns) >> return x

evalIExpr :: (ProverK loc m) => IExpr -> TcM loc m ILit
evalIExpr (ILit lit) = return lit
evalIExpr (IIdx v@(VarName t n)) = do
    mb <- tryResolveEVar noloc n t
    case mb of
        Nothing -> genTcError noloc $ text "variable binding not found"
        Just e -> expr2IExpr e >>= evalIExpr
evalIExpr (IBinOp o e1 e2) = do
    e1' <- evalIExpr e1
    e2' <- evalIExpr e2
    evalIBinOp o e1' e2'
evalIExpr (IUnOp o e1) = do
    e1' <- evalIExpr e1
    evalIUnOp o e1'
evalIExpr (ICond c e1 e2) = do
   c' <- evalIExpr c
   case c' of
       IBool True -> evalIExpr e1
       IBool False -> evalIExpr e2
evalIExpr (ISize e) = typeSize noloc (iExprTy e) >>= expr2IExpr  . fmap (Typed noloc) >>= evalIExpr

evalIBinOp :: (ProverK loc m) => IBOp -> ILit -> ILit -> TcM loc m ILit
evalIBinOp IAnd (IBool b1) (IBool b2) = return $ IBool $ b1 && b2
evalIBinOp IOr (IBool b1) (IBool b2) = return $ IBool $ b1 || b2
evalIBinOp IImplies (IBool b1) (IBool b2) = return $ IBool $ b1 <= b2
evalIBinOp IXor (IBool b1) (IBool b2) = return $ IBool $ (b1 || b2) && not (b1 && b2)
evalIBinOp (ILeq) e1 e2 = return $ IBool $ ordILit (<=) e1 e2
evalIBinOp (ILt) e1 e2 = return $ IBool $ ordILit (<) e1 e2
evalIBinOp (IGeq) e1 e2 = return $ IBool $ ordILit (>=) e1 e2
evalIBinOp (IGt) e1 e2 = return $ IBool $ ordILit (>) e1 e2
evalIBinOp (IEq) e1 e2 = return $ IBool $ ordILit (==) e1 e2
evalIBinOp (IPlus) e1 e2 = return $ numILit (+) e1 e2
evalIBinOp (IMinus) e1 e2 = return $ numILit (-) e1 e2
evalIBinOp (ITimes) e1 e2 = return $ numILit (*) e1 e2
evalIBinOp (IPower) e1 e2 = return $ integralILit (^) e1 e2
evalIBinOp (IDiv) e1 e2 = return $ integralILit div e1 e2
evalIBinOp (IMod) e1 e2 = return $ integralILit mod e1 e2

evalIUnOp :: (ProverK loc m) => IUOp -> ILit -> TcM loc m ILit
evalIUnOp INot (IBool b) = return $ IBool $ not b
evalIUnOp INeg i = return $ numILit (\x y -> -x) i (error "evalIUnOp INed")

numILit :: (forall a . Num a => a -> a -> a) -> ILit -> ILit -> ILit
numILit f (IInt8 i1)    (IInt8 i2)    = IInt8 $ f i1 i2
numILit f (IInt16 i1)   (IInt16 i2)   = IInt16 $ f i1 i2
numILit f (IInt32 i1)   (IInt32 i2)   = IInt32 $ f i1 i2
numILit f (IInt64 i1)   (IInt64 i2)   = IInt64 $ f i1 i2
numILit f (IUint8 i1)   (IUint8 i2)   = IUint8 $ f i1 i2
numILit f (IUint16 i1)  (IUint16 i2)  = IUint16 $ f i1 i2
numILit f (IUint32 i1)  (IUint32 i2)  = IUint32 $ f i1 i2
numILit f (IUint64 i1)  (IUint64 i2)  = IUint64 $ f i1 i2
numILit f (IFloat32 i1) (IFloat32 i2) = IFloat32 $ f i1 i2
numILit f (IFloat64 i1) (IFloat64 i2) = IFloat64 $ f i1 i2

integralILit :: (forall a . Integral a => a -> a -> a) -> ILit -> ILit -> ILit
integralILit f (IInt8 i1)    (IInt8 i2)    = IInt8 $ f i1 i2
integralILit f (IInt16 i1)   (IInt16 i2)   = IInt16 $ f i1 i2
integralILit f (IInt32 i1)   (IInt32 i2)   = IInt32 $ f i1 i2
integralILit f (IInt64 i1)   (IInt64 i2)   = IInt64 $ f i1 i2
integralILit f (IUint8 i1)   (IUint8 i2)   = IUint8 $ f i1 i2
integralILit f (IUint16 i1)  (IUint16 i2)  = IUint16 $ f i1 i2
integralILit f (IUint32 i1)  (IUint32 i2)  = IUint32 $ f i1 i2
integralILit f (IUint64 i1)  (IUint64 i2)  = IUint64 $ f i1 i2

ordILit :: (forall a . Ord a => a -> a -> Bool) -> ILit -> ILit -> Bool
ordILit f (IInt8 i1)    (IInt8 i2)    = f i1 i2
ordILit f (IInt16 i1)   (IInt16 i2)   = f i1 i2
ordILit f (IInt32 i1)   (IInt32 i2)   = f i1 i2
ordILit f (IInt64 i1)   (IInt64 i2)   = f i1 i2
ordILit f (IUint8 i1)   (IUint8 i2)   = f i1 i2
ordILit f (IUint16 i1)  (IUint16 i2)  = f i1 i2
ordILit f (IUint32 i1)  (IUint32 i2)  = f i1 i2
ordILit f (IUint64 i1)  (IUint64 i2)  = f i1 i2
ordILit f (IFloat32 i1) (IFloat32 i2) = f i1 i2
ordILit f (IFloat64 i1) (IFloat64 i2) = f i1 i2
ordILit f (IBool i1)    (IBool i2)    = f i1 i2
