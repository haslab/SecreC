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
import Control.Monad.State.Strict as State
import Control.Monad.Writer.Strict as Writer
import Control.Monad.Reader as Reader
import Control.Monad.Except
import Control.Monad.Trans.Control

-- * Exports

fullyEvaluateIndexExpr :: (ProverK loc m) => loc -> Expr -> TcM m Word64
fullyEvaluateIndexExpr l e = do
    IUint64 w <- fullyEvaluateExpr l $ fmap (Typed l) e
    return w

fullyEvaluateExpr :: (ProverK loc m) => loc -> Expression GIdentifier (Typed loc) -> TcM m ILit
fullyEvaluateExpr l e = evaluate l (text "evaluateExpr") (fullEvalIExpr l =<< expr2IExpr e)

fullyEvaluateIExpr :: (ProverK loc m) => loc -> IExpr -> TcM m ILit
fullyEvaluateIExpr l e = evaluate l (text "evaluateExpr") (fullEvalIExpr l e)

---- * Internal declarations

evaluate :: (ProverK loc m) => loc -> Doc -> TcM m a -> TcM m a
evaluate l doc m = do
    arr <- Reader.ask
    env <- State.get
    opts <- TcM $ lift Reader.ask
    mb <- lift $ timeout (evalTimeOut opts * 10^6) $ runSecrecMWith opts $ execTcM m arr env
    case mb of
        Nothing -> tcError (locpos l) $ Halt $ StaticEvalError doc $ Just $ TimedOut $ evalTimeOut opts
        Just (Left err) -> do
            tcError (locpos l) $ Halt $ StaticEvalError doc $ Just err
        Just (Right ((x,env'),warns)) -> do
            State.put env'
            TcM (lift $ Writer.tell warns) >> return x

fullEvalIExpr :: (ProverK loc m) => loc -> IExpr -> TcM m ILit
fullEvalIExpr l e = do
    i <- evalIExpr l e
    case i of
        ILit lit -> return lit
        otherwise -> do
            ppi <- pp i
            tcError (locpos l) $ Halt $ StaticEvalError (text "evalIExpr") $ Just $ GenericError (locpos l) (text "cannot fully evaluate index expression" <+> ppi) Nothing

evalIExpr :: (ProverK loc m) => loc -> IExpr -> TcM m IExpr
evalIExpr l (ILit lit) = return $ ILit lit
evalIExpr l (IIdx v@(VarName t (VIden n@(varIdRead -> True)))) = do
    mb <- tryResolveEVar l n t
    case mb of
        Nothing -> return $ IIdx v
        Just e -> expr2SimpleIExpr e >>= evalIExpr l
evalIExpr l (IBinOp o e1 e2) = do
    e1' <- evalIExpr l e1
    e2' <- evalIExpr l e2
    evalIBinOp l o e1' e2'
evalIExpr l (IUnOp o e1) = do
    e1' <- evalIExpr l e1
    evalIUnOp l o e1'
evalIExpr l (ICond c e1 e2) = do
   c' <- evalIExpr l c
   case c' of
       ILit (IBool True) -> evalIExpr l e1
       ILit (IBool False) -> evalIExpr l e2
       c' -> do
           e1' <- evalIExpr l e1
           e2' <- evalIExpr l e2
           return $ ICond c' e1' e2'
evalIExpr l (ISize e) = do
    e' <- evalIExpr l e
    case e' of
        (IArr _ xs) -> do
            let sz = fromInteger $ toInteger $ sum $ List.map length xs
            return $ ILit $ IUint64 sz
        otherwise -> return $ ISize e'
evalIExpr l (IShape e) = do
    e' <- evalIExpr l e
    case e' of
        IArr _ xs -> do
            let szs = List.map (fromInteger . toInteger . length) xs
            return $ ILit $ ILitArr index [List.map (IUint64) szs]
        otherwise -> return $ IShape e'
evalIExpr l e = return e

boolILit :: IExpr -> Maybe Bool
boolILit (ILit (IBool b)) = Just b
boolILit e = Nothing

evalIBinOp :: ProverK loc m => loc -> IBOp -> IExpr -> IExpr -> TcM m IExpr
evalIBinOp l IAnd (boolILit -> Just b1) (boolILit -> Just b2) = return $ ILit $ IBool $ b1 && b2
evalIBinOp l IOr (boolILit -> Just b1) (boolILit -> Just b2) = return $ ILit $ IBool $ b1 || b2
evalIBinOp l IImplies (boolILit -> Just False) b2 = return $ ILit $ IBool True
evalIBinOp l IImplies b1 (boolILit -> Just False) = return $ ILit $ IBool False
evalIBinOp l IImplies (boolILit -> Just b1) (boolILit -> Just b2) = return $ILit $ IBool $ b1 <= b2
evalIBinOp l IXor (boolILit -> Just b1) (boolILit -> Just b2) = return $ ILit $ IBool $  (b1 || b2) && not (b1 && b2)
evalIBinOp l (ILeq) (ILit e1) (ILit e2) = return $ ILit $ IBool $ ordILit (<=) e1 e2
evalIBinOp l (ILt) (ILit e1) (ILit e2) = return $ ILit $ IBool $ ordILit (<) e1 e2
evalIBinOp l (IGeq) (ILit e1) (ILit e2) = return $ ILit $ IBool $ ordILit (>=) e1 e2
evalIBinOp l (IGt) (ILit e1) (ILit e2) = return $ ILit $ IBool $ ordILit (>) e1 e2
evalIBinOp l (IEq) (ILit e1) (ILit e2) = return $ ILit $ IBool $ ordILit (==) e1 e2
evalIBinOp l (IPlus) (ILit e1) (ILit e2) = return $ ILit $ numILit (+) e1 e2
evalIBinOp l (IMinus) (ILit e1) (ILit e2) = return $ ILit $ numILit (-) e1 e2
evalIBinOp l (ITimes) (ILit e1) (ILit e2) = return $ ILit $ numILit (*) e1 e2
evalIBinOp l (IPower) (ILit e1) (ILit e2) = return $ ILit $ integralILit (^) e1 e2
evalIBinOp l (IDiv) (ILit e1) (ILit e2) = return $ ILit $ integralILit div e1 e2
evalIBinOp l (IMod) (ILit e1) (ILit e2) = return $ ILit $ integralILit mod e1 e2
evalIBinOp l op e1 e2 = return $ IBinOp op e1 e2

evalIUnOp :: ProverK loc m => loc -> IUOp -> IExpr -> TcM m IExpr
evalIUnOp l INot (boolILit -> Just b) = return $ ILit $ IBool $ not b
evalIUnOp l INeg (ILit i) = return $ ILit $ numILit (\x y -> -x) i (error "evalIUnOp INed")
evalIUnOp l op e1 = return $ IUnOp op e1

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
