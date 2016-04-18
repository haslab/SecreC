{-# LANGUAGE ViewPatterns, ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.Prover.Expression (
    expr2IExpr
    ) where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment hiding (addVar)
import {-# SOURCE #-} Language.SecreC.Transformation.Simplify
import {-# SOURCE #-} Language.SecreC.Prover.Semantics
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type

import Data.Map(Map(..))
import qualified Data.Map as Map
import Data.List as List

import Control.Monad.Trans
import Control.Monad.State as State

import Text.PrettyPrint

--(assigned value,declared type)
type ExprSt = Map VarIdentifier (Maybe IExpr,Maybe Type)

type ExprM loc m = StateT ExprSt (TcM loc m)

runExprM :: (ProverK loc m) => ExprM loc m a -> TcM loc m a
runExprM m = evalStateT m Map.empty

addVar x y = State.modify $ \env -> Map.insertWith mergeVar x y env
    where
    mergeVar (e,t) (e',t') = (maybe e Just e',maybe t Just t')

-- discard local variable declarations
localExprM :: (ProverK loc m) => ExprM loc m a -> ExprM loc m a
localExprM m = do
    vs <- State.get
    -- undeclare all variable
    State.put $ Map.map (\(e,t) -> (e,Nothing)) vs
    x <- m
    State.modify $ \vs' -> addLocals vs vs'
    return x
  where
    addLocals = Map.mergeWithKey (\l x y -> Just $ merge x y) id (const Map.empty)
    merge x (e',Just t') = x
    merge (e,Just t) (e',Nothing) = (mergeE e e',Just t)
    merge (e,Nothing) (e',Nothing) = (mergeE e e',Nothing)
    mergeE x y = maybe x Just y

expr2IExpr :: (ProverK loc m) => Expression VarIdentifier (Typed loc) -> TcM loc m IExpr
expr2IExpr e = runExprM $ do
    let l = unTyped $ loc e
    substs <- lift getTSubsts 
    subste <- lift $ substFromTSubsts "simplify" l substs False Map.empty e
    (ss',mbe') <- lift $ simplifyExpression subste
    stmts2Prover ss'
    case mbe' of
        Nothing -> lift $ genTcError (locpos l) $ text "failed to convert void expression" <+> pp e <+> text "to prover expression"
        Just e' -> expr2Prover e'

stmts2Prover :: (ProverK loc m) => [Statement VarIdentifier (Typed loc)] -> ExprM loc m ()
stmts2Prover = mapM_ stmt2Prover

stmt2Prover :: (ProverK loc m) => Statement VarIdentifier (Typed loc) -> ExprM loc m ()
stmt2Prover (CompoundStatement l ss) = localExprM $ stmts2Prover ss
stmt2Prover (VarStatement l (VariableDeclaration _ t vs)) = mapM_ varInit2Prover vs
stmt2Prover (AssertStatement {}) = return ()
stmt2Prover (SyscallStatement l n args) = syscall2Prover (unTyped l) n args
stmt2Prover (ExpressionStatement l e) = expr2ProverMb e >> return ()
stmt2Prover s = lift $ genTcError (locpos $ unTyped $ loc s) $ text "failed to convert statement" <+> pp s <+> text "to prover expression"
    
syscall2Prover :: (ProverK loc m) => loc -> String -> [SyscallParameter VarIdentifier (Typed loc)] -> ExprM loc m ()
syscall2Prover l n@(isPrefixOf "core." -> True) args = do
    args' <- mapM unpush $ init args
    VarName (Typed _ t) r <- unret $ last args
    ie <- corecall2Prover l (drop 5 n) args' t
    addVar r (Just ie,Nothing)
  where
    unpush (SyscallPush _ e) = expr2Prover e
    unret (SyscallReturn _ v) = return v
syscall2Prover l n args = lift $ genTcError (locpos l) $ text "unsupported syscall" <+> pp n <+> sepBy space (map pp args)
    
corecall2Prover :: ProverK loc m => loc -> String -> [IExpr] -> Type -> ExprM loc m IExpr
corecall2Prover l "sub_int8"    [e1,e2] (BaseT (TyPrim (DatatypeInt8 _)))    = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_int16"   [e1,e2] (BaseT (TyPrim (DatatypeInt16 _)))   = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_int32"   [e1,e2] (BaseT (TyPrim (DatatypeInt32 _)))   = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_int64"   [e1,e2] (BaseT (TyPrim (DatatypeInt64 _)))   = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_uint8"   [e1,e2] (BaseT (TyPrim (DatatypeUint8 _)))   = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_uint16"  [e1,e2] (BaseT (TyPrim (DatatypeUint16 _)))  = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_uint32"  [e1,e2] (BaseT (TyPrim (DatatypeUint32 _)))  = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_uint64"  [e1,e2] (BaseT (TyPrim (DatatypeUint64 _)))  = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_float32" [e1,e2] (BaseT (TyPrim (DatatypeFloat32 _))) = return $ IBinOp IMinus e1 e2
corecall2Prover l "sub_float64" [e1,e2] (BaseT (TyPrim (DatatypeFloat64 _))) = return $ IBinOp IMinus e1 e2
corecall2Prover l "add_int8"    [e1,e2] (BaseT (TyPrim (DatatypeInt8 _)))    = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_int16"   [e1,e2] (BaseT (TyPrim (DatatypeInt16 _)))   = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_int32"   [e1,e2] (BaseT (TyPrim (DatatypeInt32 _)))   = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_int64"   [e1,e2] (BaseT (TyPrim (DatatypeInt64 _)))   = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_uint8"   [e1,e2] (BaseT (TyPrim (DatatypeUint8 _)))   = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_uint16"  [e1,e2] (BaseT (TyPrim (DatatypeUint16 _)))  = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_uint32"  [e1,e2] (BaseT (TyPrim (DatatypeUint32 _)))  = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_uint64"  [e1,e2] (BaseT (TyPrim (DatatypeUint64 _)))  = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_float32" [e1,e2] (BaseT (TyPrim (DatatypeFloat32 _))) = return $ IBinOp IPlus e1 e2
corecall2Prover l "add_float64" [e1,e2] (BaseT (TyPrim (DatatypeFloat64 _))) = return $ IBinOp IPlus e1 e2
corecall2Prover l "mul_int8"    [e1,e2] (BaseT (TyPrim (DatatypeInt8 _)))    = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_int16"   [e1,e2] (BaseT (TyPrim (DatatypeInt16 _)))   = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_int32"   [e1,e2] (BaseT (TyPrim (DatatypeInt32 _)))   = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_int64"   [e1,e2] (BaseT (TyPrim (DatatypeInt64 _)))   = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_uint8"   [e1,e2] (BaseT (TyPrim (DatatypeUint8 _)))   = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_uint16"  [e1,e2] (BaseT (TyPrim (DatatypeUint16 _)))  = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_uint32"  [e1,e2] (BaseT (TyPrim (DatatypeUint32 _)))  = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_uint64"  [e1,e2] (BaseT (TyPrim (DatatypeUint64 _)))  = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_float32" [e1,e2] (BaseT (TyPrim (DatatypeFloat32 _))) = return $ IBinOp ITimes e1 e2
corecall2Prover l "mul_float64" [e1,e2] (BaseT (TyPrim (DatatypeFloat64 _))) = return $ IBinOp ITimes e1 e2
corecall2Prover l "leq_int8" [e1,e2] (BaseT (TyPrim (DatatypeInt8 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_int16" [e1,e2] (BaseT (TyPrim (DatatypeInt16 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_int32" [e1,e2] (BaseT (TyPrim (DatatypeInt32 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_int64" [e1,e2] (BaseT (TyPrim (DatatypeInt64 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_uint8" [e1,e2] (BaseT (TyPrim (DatatypeUint8 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_uint16" [e1,e2] (BaseT (TyPrim (DatatypeUint16 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_uint32" [e1,e2] (BaseT (TyPrim (DatatypeUint32 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_uint64" [e1,e2] (BaseT (TyPrim (DatatypeUint64 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_float32" [e1,e2] (BaseT (TyPrim (DatatypeFloat32 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_float64" [e1,e2] (BaseT (TyPrim (DatatypeFloat64 _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "leq_bool" [e1,e2] (BaseT (TyPrim (DatatypeBool _))) = return $ IBinOp ILeq e1 e2
corecall2Prover l "eq_int8" [e1,e2] (BaseT (TyPrim (DatatypeInt8 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_int16" [e1,e2] (BaseT (TyPrim (DatatypeInt16 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_int32" [e1,e2] (BaseT (TyPrim (DatatypeInt32 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_int64" [e1,e2] (BaseT (TyPrim (DatatypeInt64 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_uint8" [e1,e2] (BaseT (TyPrim (DatatypeUint8 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_uint16" [e1,e2] (BaseT (TyPrim (DatatypeUint16 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_uint32" [e1,e2] (BaseT (TyPrim (DatatypeUint32 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_uint64" [e1,e2] (BaseT (TyPrim (DatatypeUint64 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_float32" [e1,e2] (BaseT (TyPrim (DatatypeFloat32 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_float64" [e1,e2] (BaseT (TyPrim (DatatypeFloat64 _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "eq_bool" [e1,e2] (BaseT (TyPrim (DatatypeBool _))) = return $ IBinOp IEq e1 e2
corecall2Prover l "neq_int8" [e1,e2] (BaseT (TyPrim (DatatypeInt8 _))) = return $ IUnOp INot $ IBinOp IEq e1 e2
corecall2Prover l "neq_int16" [e1,e2] (BaseT (TyPrim (DatatypeInt16 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_int32" [e1,e2] (BaseT (TyPrim (DatatypeInt32 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_int64" [e1,e2] (BaseT (TyPrim (DatatypeInt64 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_uint8" [e1,e2] (BaseT (TyPrim (DatatypeUint8 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_uint16" [e1,e2] (BaseT (TyPrim (DatatypeUint16 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_uint32" [e1,e2] (BaseT (TyPrim (DatatypeUint32 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_uint64" [e1,e2] (BaseT (TyPrim (DatatypeUint64 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_float32" [e1,e2] (BaseT (TyPrim (DatatypeFloat32 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_float64" [e1,e2] (BaseT (TyPrim (DatatypeFloat64 _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "neq_bool" [e1,e2] (BaseT (TyPrim (DatatypeBool _))) = return $ IBinOp INeq e1 e2
corecall2Prover l "size" [e] t = do
    dim <- lift $ typeDim l t >>= evaluateIndexExpr l
    case dim of
        0 -> return $ ILit $ IUint64 1
        otherwise -> return $ ISize e
corecall2Prover l n es t = lift $ genTcError (locpos l) $ text "failed to convert core call" <+> pp n <+> parens (sepBy comma $ map pp es) <+> text "to prover expression"
    
varInit2Prover :: (ProverK loc m) => VariableInitialization VarIdentifier (Typed loc) -> ExprM loc m ()
varInit2Prover (VariableInitialization _ v@(VarName l n) _ e) = do
    ie <- mapM expr2Prover e
    addVar n (ie,Just $ typed l)

expr2ProverMb :: (ProverK loc m) => Expression VarIdentifier (Typed loc) -> ExprM loc m (Maybe IExpr)
expr2ProverMb (RVariablePExpr l v@(VarName tl n)) = do
    vs <- State.get
    case Map.lookup n vs of
        Just (Nothing,_) -> return $ Just $ IIdx $ fmap typed v
        Just (Just ie,_) -> return $ Just ie
        otherwise -> return $ Just $ IIdx $ fmap typed v
expr2ProverMb (LitPExpr l lit) = liftM Just $ lit2Prover lit
expr2ProverMb (CondExpr l c e1 e2) = do
    c' <- expr2Prover c
    e1' <- expr2Prover e1
    e2' <- expr2Prover e2
    return $ Just $ ICond c' e1' e2'
expr2ProverMb (BinaryAssign l lhs (BinaryAssignEqual _) e) = do
    IIdx (VarName _ v) <- expr2Prover lhs
    ie <- expr2Prover e
    addVar v (Just ie,Nothing)
    return Nothing
expr2ProverMb e = lift $ genTcError (locpos $ unTyped $ loc e) $ text "failed to convert expression" <+> pp e <+> text "to prover expression"
    
expr2Prover :: (ProverK loc m) => Expression VarIdentifier (Typed loc) -> ExprM loc m IExpr
expr2Prover e = do
    mb <- expr2ProverMb e
    case mb of
        Nothing -> lift $ genTcError (locpos $ unTyped $ loc e) $ text "failed to convert void expression" <+> pp e <+> text "to prover expression"
        Just e' -> return e'
    
lit2Prover :: (ProverK loc m) => Literal (Typed loc) -> ExprM loc m IExpr
lit2Prover lit@(IntLit (Typed l (BaseT (TyPrim t))) i) = case t of
    DatatypeInt8 _ -> return $ ILit $ IInt8 $ fromInteger i
    DatatypeInt16 _ -> return $ ILit $ IInt16 $ fromInteger i
    DatatypeInt32 _ -> return $ ILit $ IInt32 $ fromInteger i
    DatatypeInt64 _ -> return $ ILit $ IInt64 $ fromInteger i
    DatatypeUint8 _ -> return $ ILit $ IUint8 $ fromInteger i
    DatatypeUint16 _ -> return $ ILit $ IUint16 $ fromInteger i
    DatatypeUint32 _ -> return $ ILit $ IUint32 $ fromInteger i
    DatatypeUint64 _ -> return $ ILit $ IUint64 $ fromInteger i
    DatatypeXorUint8 _ -> return $ ILit $ IUint8 $ fromInteger i
    DatatypeXorUint16 _ -> return $ ILit $ IUint16 $ fromInteger i
    DatatypeXorUint32 _ -> return $ ILit $ IUint32 $ fromInteger i
    DatatypeXorUint64 _ -> return $ ILit $ IUint64 $ fromInteger i
    otherwise -> lift $ genTcError (locpos l) $ text "failed to convert literal" <+> pp lit <+> text "to prover expression"
lit2Prover lit@(FloatLit (Typed l (BaseT (TyPrim t))) f) = case t of
    DatatypeFloat32 _ -> return $ ILit $ IFloat32 $ realToFrac f
    DatatypeFloat64 _ -> return $ ILit $ IFloat64 $ realToFrac f
    otherwise -> lift $ genTcError (locpos l) $ text "failed to convert literal" <+> pp lit <+> text "to prover expression"
lit2Prover lit@(StringLit (Typed l (BaseT (TyPrim t))) s) = case t of
    otherwise -> lift $ genTcError (locpos l) $ text "failed to convert literal" <+> pp lit <+> text "to prover expression"
lit2Prover lit@(BoolLit (Typed l (BaseT (TyPrim t))) b) = case t of
    DatatypeBool _ -> return $ ILit $ IBool b
    otherwise -> lift $ genTcError (locpos l) $ text "failed to convert literal" <+> pp lit <+> text "to prover expression"
lit2Prover lit = lift $ genTcError (locpos $ loc lit) $ text "failed to convert literal" <+> pp lit <> text "::" <> pp (typed $ loc lit) <+> text "to prover expression"



