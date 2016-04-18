{-# LANGUAGE DeriveDataTypeable, ViewPatterns, FlexibleContexts, GADTs #-}

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
evalIBinOp IXor (IBool b1) (IBool b2) = return $ IBool $ (b1 || b2) && not (b1 && b2)
evalIBinOp (ILeq) e1 e2 = evalILeq e1 e2
evalIBinOp (IEq) e1 e2 = evalIEq e1 e2
evalIBinOp (IPlus) e1 e2 = evalIPlus e1 e2
evalIBinOp (IMinus) e1 e2 = evalIMinus e1 e2
evalIBinOp (ITimes) e1 e2 = evalITimes e1 e2
evalIBinOp (IPower) e1 e2 = evalIPower e1 e2
evalIBinOp (IDiv) e1 e2 = evalIDiv e1 e2
evalIBinOp (IMod) e1 e2 = evalIMod e1 e2

evalIUnOp :: (ProverK loc m) => IUOp -> ILit -> TcM loc m ILit
evalIUnOp INot (IBool b) = return $ IBool $ not b
evalIUnOp (INeg) i = evalINeg i

evalINeg :: ProverK loc m => ILit -> TcM loc m ILit
evalINeg (IInt8 i) = return $ IInt8 (-i)
evalINeg (IInt16 i) = return $ IInt16 (-i)
evalINeg (IInt32 i) = return $ IInt32 (-i)
evalINeg (IInt64 i) = return $ IInt64 (-i)
evalINeg (IUint8 i) = return $ IUint8 (-i)
evalINeg (IUint16 i) = return $ IUint16 (-i)
evalINeg (IUint32 i) = return $ IUint32 (-i)
evalINeg (IUint64 i) = return $ IUint64 (-i)
evalINeg (IFloat32 i) = return $ IFloat32 (-i)
evalINeg (IFloat64 i) = return $ IFloat64 (-i)
evalINeg i = genTcError noloc $ text "failed to evaluate negation for" <+> pp i

evalILeq :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalILeq (IInt8 i1) (IInt8 i2) = return $ IBool (i1 <= i2)
evalILeq (IInt16 i1) (IInt16 i2) = return $ IBool (i1 <= i2)
evalILeq (IInt32 i1) (IInt32 i2) = return $ IBool (i1 <= i2)
evalILeq (IInt64 i1) (IInt64 i2) = return $ IBool (i1 <= i2)
evalILeq (IUint8 i1) (IUint8 i2) = return $ IBool (i1 <= i2)
evalILeq (IUint16 i1) (IUint16 i2) = return $ IBool (i1 <= i2)
evalILeq (IUint32 i1) (IUint32 i2) = return $ IBool (i1 <= i2)
evalILeq (IUint64 i1) (IUint64 i2) = return $ IBool (i1 <= i2)
evalILeq (IFloat32 i1) (IFloat32 i2) = return $ IBool (i1 <= i2)
evalILeq (IFloat64 i1) (IFloat64 i2) = return $ IBool (i1 <= i2)
evalILeq (IBool i1) (IBool i2) = return $ IBool (i1 <= i2)
evalILeq i1 i2 = genTcError noloc $ text "failed to evaluate leq for" <+> pp i1 <+> pp i2

evalIEq :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalIEq (IInt8 i1) (IInt8 i2) = return $ IBool (i1 == i2)
evalIEq (IInt16 i1) (IInt16 i2) = return $ IBool (i1 == i2)
evalIEq (IInt32 i1) (IInt32 i2) = return $ IBool (i1 == i2)
evalIEq (IInt64 i1) (IInt64 i2) = return $ IBool (i1 == i2)
evalIEq (IUint8 i1) (IUint8 i2) = return $ IBool (i1 == i2)
evalIEq (IUint16 i1) (IUint16 i2) = return $ IBool (i1 == i2)
evalIEq (IUint32 i1) (IUint32 i2) = return $ IBool (i1 == i2)
evalIEq (IUint64 i1) (IUint64 i2) = return $ IBool (i1 == i2)
evalIEq (IFloat32 i1) (IFloat32 i2) = return $ IBool (i1 == i2)
evalIEq (IFloat64 i1) (IFloat64 i2) = return $ IBool (i1 == i2)
evalIEq (IBool i1) (IBool i2) = return $ IBool (i1 == i2)
evalIEq i1 i2 = genTcError noloc $ text "failed to evaluate eq for" <+> pp i1 <+> pp i2

evalIPlus :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalIPlus (IInt8 i1) (IInt8 i2) = return $ IInt8 (i1 + i2)
evalIPlus (IInt16 i1) (IInt16 i2) = return $ IInt16 (i1 + i2)
evalIPlus (IInt32 i1) (IInt32 i2) = return $ IInt32 (i1 + i2)
evalIPlus (IInt64 i1) (IInt64 i2) = return $ IInt64 (i1 + i2)
evalIPlus (IUint8 i1) (IUint8 i2) = return $ IUint8 (i1 + i2)
evalIPlus (IUint16 i1) (IUint16 i2) = return $ IUint16 (i1 + i2)
evalIPlus (IUint32 i1) (IUint32 i2) = return $ IUint32 (i1 + i2)
evalIPlus (IUint64 i1) (IUint64 i2) = return $ IUint64 (i1 + i2)
evalIPlus (IFloat32 i1) (IFloat32 i2) = return $ IFloat32 (i1 + i2)
evalIPlus (IFloat64 i1) (IFloat64 i2) = return $ IFloat64 (i1 + i2)
evalIPlus i1 i2 = genTcError noloc $ text "failed to evaluate plus for" <+> pp i1 <+> pp i2

evalIMinus :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalIMinus (IInt8 i1) (IInt8 i2) = return $ IInt8 (i1 - i2)
evalIMinus (IInt16 i1) (IInt16 i2) = return $ IInt16 (i1 - i2)
evalIMinus (IInt32 i1) (IInt32 i2) = return $ IInt32 (i1 - i2)
evalIMinus (IInt64 i1) (IInt64 i2) = return $ IInt64 (i1 - i2)
evalIMinus (IUint8 i1) (IUint8 i2) = return $ IUint8 (i1 - i2)
evalIMinus (IUint16 i1) (IUint16 i2) = return $ IUint16 (i1 - i2)
evalIMinus (IUint32 i1) (IUint32 i2) = return $ IUint32 (i1 - i2)
evalIMinus (IUint64 i1) (IUint64 i2) = return $ IUint64 (i1 - i2)
evalIMinus (IFloat32 i1) (IFloat32 i2) = return $ IFloat32 (i1 - i2)
evalIMinus (IFloat64 i1) (IFloat64 i2) = return $ IFloat64 (i1 - i2)
evalIMinus i1 i2 = genTcError noloc $ text "failed to evaluate minus for" <+> pp i1 <+> pp i2

evalITimes :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalITimes (IInt8 i1) (IInt8 i2) = return $ IInt8 (i1 * i2)
evalITimes (IInt16 i1) (IInt16 i2) = return $ IInt16 (i1 * i2)
evalITimes (IInt32 i1) (IInt32 i2) = return $ IInt32 (i1 * i2)
evalITimes (IInt64 i1) (IInt64 i2) = return $ IInt64 (i1 * i2)
evalITimes (IUint8 i1) (IUint8 i2) = return $ IUint8 (i1 * i2)
evalITimes (IUint16 i1) (IUint16 i2) = return $ IUint16 (i1 * i2)
evalITimes (IUint32 i1) (IUint32 i2) = return $ IUint32 (i1 * i2)
evalITimes (IUint64 i1) (IUint64 i2) = return $ IUint64 (i1 * i2)
evalITimes (IFloat32 i1) (IFloat32 i2) = return $ IFloat32 (i1 * i2)
evalITimes (IFloat64 i1) (IFloat64 i2) = return $ IFloat64 (i1 * i2)
evalITimes i1 i2 = genTcError noloc $ text "failed to evaluate times for" <+> pp i1 <+> pp i2

evalIDiv :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalIDiv (IInt8 i1) (IInt8 i2) = return $ IInt8 (i1 `div` i2)
evalIDiv (IInt16 i1) (IInt16 i2) = return $ IInt16 (i1 `div` i2)
evalIDiv (IInt32 i1) (IInt32 i2) = return $ IInt32 (i1 `div` i2)
evalIDiv (IInt64 i1) (IInt64 i2) = return $ IInt64 (i1 `div` i2)
evalIDiv (IUint8 i1) (IUint8 i2) = return $ IUint8 (i1 `div` i2)
evalIDiv (IUint16 i1) (IUint16 i2) = return $ IUint16 (i1 `div` i2)
evalIDiv (IUint32 i1) (IUint32 i2) = return $ IUint32 (i1 `div` i2)
evalIDiv (IUint64 i1) (IUint64 i2) = return $ IUint64 (i1 `div` i2)
evalIDiv i1 i2 = genTcError noloc $ text "failed to evaluate div for" <+> pp i1 <+> pp i2

evalIPower :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalIPower (IInt8 i1) (IInt8 i2) = return $ IInt8 (i1 ^ i2)
evalIPower i1 i2 = genTcError noloc $ text "failed to evaluate power for" <+> pp i1 <+> pp i2

evalIMod :: ProverK loc m => ILit -> ILit -> TcM loc m ILit
evalIMod (IInt8 i1) (IInt8 i2) = return $ IInt8 (i1 `mod` i2)
evalIMod (IInt16 i1) (IInt16 i2) = return $ IInt16 (i1 `mod` i2)
evalIMod (IInt32 i1) (IInt32 i2) = return $ IInt32 (i1 `mod` i2)
evalIMod (IInt64 i1) (IInt64 i2) = return $ IInt64 (i1 `mod` i2)
evalIMod (IUint8 i1) (IUint8 i2) = return $ IUint8 (i1 `mod` i2)
evalIMod (IUint16 i1) (IUint16 i2) = return $ IUint16 (i1 `mod` i2)
evalIMod (IUint32 i1) (IUint32 i2) = return $ IUint32 (i1 `mod` i2)
evalIMod (IUint64 i1) (IUint64 i2) = return $ IUint64 (i1 `mod` i2)
evalIMod i1 i2 = genTcError noloc $ text "failed to evaluate mod for" <+> pp i1 <+> pp i2
