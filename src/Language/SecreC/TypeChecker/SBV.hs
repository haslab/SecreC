
module Language.SecreC.TypeChecker.SBV where

import Data.SBV

import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map
import Control.Monad.State as State
import Control.Monad.Reader as Reader

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Index
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import Language.SecreC.Pretty

type SBVVars = (Map VarIdentifier SInteger,Map VarIdentifier SBool)

getSIntegerVar :: VarIdentifier -> Reader SBVVars SInteger
getSIntegerVar v = do
	(ints,bools) <- Reader.ask
	case Map.lookup v ints of
		Just i -> return i
		otherwise -> error $ "no SInteger variable " ++ ppr v ++  " found "
getSBoolVar :: VarIdentifier -> Reader SBVVars SBool
getSBoolVar v = do
	(ints,bools) <- Reader.ask
	case Map.lookup v bools of
		Just b -> return b
		otherwise -> error $ "no SBool variable " ++ ppr v ++ " found"

cond2SBV :: ICond VarIdentifier -> Reader SBVVars SBool
cond2SBV ex = case ex of
	IBool b -> return $ fromBool b
	IBInd v -> getSBoolVar v
	INot e -> liftM bnot $ cond2SBV e
	IAnd e -> liftM bAnd $ mapM cond2SBV e
	IBoolOp op e1 e2 -> do
		b1 <- cond2SBV e1
		b2 <- cond2SBV e2
		return $ bOp2SBV op b1 b2
	ILeq e -> liftM (0 .<=) (expr2SBV e)
	IEq e -> liftM (0 .==) (expr2SBV e)

expr2SBV :: IExpr VarIdentifier -> Reader SBVVars SInteger
expr2SBV ex = case ex of 
	IInt n -> return $ literal n
	IIdx v -> getSIntegerVar v
	ISum e -> aux e
	IArith op e1 e2 -> do
		x1 <- expr2SBV e1
		x2 <- expr2SBV e2
		return (aOp2SBV op x1 x2)
	ISym e -> liftM ((-1) *) (expr2SBV e)
  where
	aux [e] = expr2SBV e
	aux (e:es) = do
		x <- expr2SBV e
		y <- aux es
		return (x + y)
	aux _ = error "<expr2Y>"

aOp2SBV :: IAOp -> (SInteger -> SInteger -> SInteger)
aOp2SBV IMinus = (-)
aOp2SBV ITimes = (*)
aOp2SBV IPower = (.^)
aOp2SBV IDiv   = sDiv
aOp2SBV IModOp = sMod

bOp2SBV :: Boolean b => IBOp -> (b -> b -> b)
bOp2SBV IOr = (|||)
bOp2SBV IXor = (<+>)

type2SBV :: VarIdentifier -> Type -> Symbolic (SBVVars -> SBVVars)
type2SBV v t | isBoolType t = type2SBool v
             | isIntType t = type2SInteger v
             | otherwise = error "type2SBV"

type2SInteger, type2SBool :: VarIdentifier -> Symbolic (SBVVars -> SBVVars)
type2SInteger v = do
	i <- sInteger (ppr v)
	return $ \(ints,bools) -> (Map.insert v i ints,bools)
type2SBool v = do
	b <- sBool (ppr v)
	return $ \(ints,bools) -> (ints,Map.insert v b bools)

