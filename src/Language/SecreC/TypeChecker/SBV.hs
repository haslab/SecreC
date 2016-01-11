{-# LANGUAGE DoAndIfThenElse, FlexibleContexts #-}

module Language.SecreC.TypeChecker.SBV where

import Data.SBV hiding ((<+>))
import qualified Data.SBV as SBV

import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map
import Control.Monad.State as State
import Control.Monad.Reader as Reader

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Index
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Vars

import Text.PrettyPrint

sbvError :: SecrecError -> a
sbvError err = error $ ppr err

type SBVVars = (Map VarIdentifier SInteger,Map VarIdentifier SBool)

getSIntegerVar :: Location loc => loc -> VarIdentifier -> Reader SBVVars SInteger
getSIntegerVar l v = do
	(ints,bools) <- Reader.ask
	case Map.lookup v ints of
		Just i -> return i
		otherwise -> sbvError $ TypecheckerError (locpos l) $ NotSupportedIndexOp (pp v) $ Just $ GenericError (locpos l) $ text "no SInteger variable" <+> pp v <+> text "found"
        
getSBoolVar :: Location loc => loc -> VarIdentifier -> Reader SBVVars SBool
getSBoolVar l v = do
	(ints,bools) <- Reader.ask
	case Map.lookup v bools of
		Just b -> return b
		otherwise -> sbvError $ TypecheckerError (locpos l) $ NotSupportedIndexOp (pp v) $ Just $ GenericError (locpos l) $ text "no SBool variable" <+> pp v <+> text "found"

cond2SBV :: Location loc => loc -> ICond VarIdentifier -> Reader SBVVars SBool
cond2SBV l ex = case ex of
	IBool b -> return $ fromBool b
	IBInd v -> getSBoolVar l v
	INot e -> liftM bnot $ cond2SBV l e
	IAnd e -> liftM bAnd $ mapM (cond2SBV l) e
	IBoolOp op e1 e2 -> do
		b1 <- cond2SBV l e1
		b2 <- cond2SBV l e2
		return $ bOp2SBV op b1 b2
	ILeq e -> liftM (0 .<=) (expr2SBV l e)
	IEq e -> liftM (0 .==) (expr2SBV l e)

expr2SBV :: Location loc => loc -> IExpr VarIdentifier -> Reader SBVVars SInteger
expr2SBV l ex = case ex of 
	IInt n -> return $ literal n
	IIdx v -> getSIntegerVar l v
	ISum e -> aux e
	IArith op e1 e2 -> do
		x1 <- expr2SBV l e1
		x2 <- expr2SBV l e2
		return (aOp2SBV op x1 x2)
	ISym e -> liftM ((-1) *) (expr2SBV l e)
  where
	aux [e] = expr2SBV l e
	aux (e:es) = do
		x <- expr2SBV l e
		y <- aux es
		return (x + y)
	aux es = sbvError $ TypecheckerError (locpos l) $ NotSupportedIndexOp (parens $ sepBy comma $ map pp es) $ Just $ GenericError (locpos l) $ text "<expr2Y>"

aOp2SBV :: IAOp -> (SInteger -> SInteger -> SInteger)
aOp2SBV IMinus = (-)
aOp2SBV ITimes = (*)
aOp2SBV IPower = (.^)
aOp2SBV IDiv   = sDiv
aOp2SBV IModOp = sMod

bOp2SBV :: Boolean b => IBOp -> (b -> b -> b)
bOp2SBV IOr = (|||)
bOp2SBV IXor = (SBV.<+>)

type2SBV :: (Vars (TcM loc) loc,Location loc) => loc -> VarIdentifier -> Type -> TcM loc (Symbolic (SBVVars -> SBVVars))
type2SBV l v t = do
    isB <- isBoolTypeM l t
    if isB then return $ type2SBool v
    else do
        isI <- isIntTypeM l t
        if isI then return $ type2SInteger v
        else tcError (locpos l) $ NotSupportedIndexOp (pp v) $ Just $ GenericError (locpos l) $ text "Not an index type:" <+> pp t

type2SInteger, type2SBool :: VarIdentifier -> Symbolic (SBVVars -> SBVVars)
type2SInteger v = do
	i <- sInteger (ppr v)
	return $ \(ints,bools) -> (Map.insert v i ints,bools)
type2SBool v = do
	b <- sBool (ppr v)
	return $ \(ints,bools) -> (ints,Map.insert v b bools)

