{-# LANGUAGE GADTs, ViewPatterns, ConstraintKinds, FlexibleContexts #-}

module Language.SecreC.Prover.Expression (
    expr2IExpr, expr2SimpleIExpr
    ) where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.TypeChecker.Environment hiding (addVar)
import {-# SOURCE #-} Language.SecreC.Transformation.Simplify
import {-# SOURCE #-} Language.SecreC.Prover.Semantics
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint

import Data.Map(Map(..))
import qualified Data.Map as Map
import Data.List as List

import Control.Monad.Trans
import Control.Monad.State as State

import Text.PrettyPrint

--(assigned value,declared type)
type ExprSt = Map VarIdentifier (Maybe IExpr,Maybe Type)

type ExprM m = StateT ExprSt (TcM m)

runExprM :: Monad m => ExprM m a -> TcM m a
runExprM m = evalStateT m Map.empty

addVar x y = State.modify $ \env -> Map.insertWith mergeVar x y env
    where
    mergeVar (e,t) (e',t') = (maybe e Just e',maybe t Just t')

-- discard local variable declarations
localExprM :: Monad m => ExprM m a -> ExprM m a
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

expr2SimpleIExpr :: (ProverK loc m) => Expression GIdentifier (Typed loc) -> TcM m IExpr
expr2SimpleIExpr e = expr2IExpr e >>= evalIExpr (unTyped $ loc e)

expr2IExpr :: (ProverK loc m) => Expression GIdentifier (Typed loc) -> TcM m IExpr
expr2IExpr e = runExprM $ do
    let l = unTyped $ loc e
    substs <- lift $ getTSubsts l
    subste <- lift $ substFromTSubsts "simplify" dontStop l substs False Map.empty e
    (ss',mbe') <- lift $ runSimplify $ simplifyExpression False Nothing subste
    stmts2Prover ss'
    case mbe' of
        Nothing -> lift $ do
            ppe <- pp e
            genTcError (locpos l) True $ text "failed to convert void expression" <+> ppe <+> text "to prover expression"
        Just e' -> expr2Prover e'

stmts2Prover :: (ProverK loc m) => [Statement GIdentifier (Typed loc)] -> ExprM m ()
stmts2Prover = mapM_ stmt2Prover

stmt2Prover :: (ProverK loc m) => Statement GIdentifier (Typed loc) -> ExprM m ()
stmt2Prover (CompoundStatement l ss) = localExprM $ stmts2Prover ss
stmt2Prover (VarStatement l (VariableDeclaration _ isConst isHavoc t vs)) = mapM_ (varInit2Prover (unTyped l) isConst isHavoc) vs
stmt2Prover (AssertStatement {}) = return ()
stmt2Prover (SyscallStatement l n args) = syscall2Prover (unTyped l) n args
stmt2Prover (ExpressionStatement l e) = expr2ProverMb e >> return ()
stmt2Prover (AnnStatement l ann) = return ()
stmt2Prover s = lift $ do
    pps <- pp s
    genTcError (locpos $ unTyped $ loc s) True $ text "failed to convert statement" <+> pps <+> text "to prover expression"
    
syscall2Prover :: (ProverK loc m) => loc -> String -> [SyscallParameter GIdentifier (Typed loc)] -> ExprM m ()
syscall2Prover l n@(isPrefixOf "core." -> True) args = do
    args' <- mapM unpush $ init args
    VarName (Typed _ t) (VIden r) <- unret $ last args
    ie <- corecall2Prover l (drop 5 n) args'
    addVar r (Just ie,Nothing)
  where
    unpush (SyscallPush _ e) = variadicExpr2Prover e
    unret (SyscallReturn _ v) = return v
syscall2Prover l n args = lift $ do
    ppn <- pp n
    ppargs <- mapM pp args
    genTcError (locpos l) False $ text "unsupported syscall" <+> ppn <+> sepBy space ppargs
    
builtin2Prover :: ProverK loc m => loc -> String -> [(Expression GIdentifier (Typed loc),IsVariadic)] -> ExprM m (Maybe IExpr)
builtin2Prover l n@(isPrefixOf "core." -> True) args = do
    args' <- mapM variadicExpr2Prover args
    liftM Just $ corecall2Prover l (drop 5 n) args'
builtin2Prover l n args = lift $ do
    ppn <- pp n
    ppargs <- mapM pp args
    genTcError (locpos l) False $ text "unsupported builtin" <+> ppn <+> sepBy space ppargs
    
corecall2Prover :: ProverK loc m => loc -> String -> [IExpr] -> ExprM m IExpr
corecall2Prover l "sub"    [e1,e2] = return $ IBinOp IMinus e1 e2
corecall2Prover l "add"    [e1,e2] = return $ IBinOp IPlus e1 e2
corecall2Prover l "mul"    [e1,e2] = return $ IBinOp ITimes e1 e2
corecall2Prover l "leq"    [e1,e2] = return $ IBinOp ILeq e1 e2
corecall2Prover l "geq"    [e1,e2] = return $ IBinOp IGeq e1 e2
corecall2Prover l "eq"     [e1,e2] = return $ IBinOp IEq e1 e2
corecall2Prover l "neq"    [e1,e2] = return $ IUnOp INot $ IBinOp IEq e1 e2
corecall2Prover l "gt"    [e1,e2] = return $ IBinOp IGt e1 e2
corecall2Prover l "lt"    [e1,e2] = return $ IBinOp ILt e1 e2
corecall2Prover l "implies"    [e1,e2] = return $ IBinOp IImplies e1 e2
corecall2Prover l "size"        [e]     = do
    dim <- lift $ typeDim l (iExprTy e) >>= fullyEvaluateIndexExpr l
    case dim of
        0 -> return $ ILit $ IUint64 1
        otherwise -> return $ ISize e
corecall2Prover l n es = lift $ do
    ppn <- pp n
    pp2 <- mapM pp es
    genTcError (locpos l) False $ text "failed to convert core call" <+> ppn <+> parens (sepBy comma pp2) <+> text "to prover expression"
    
varInit2Prover :: (ProverK loc m) => loc -> Bool -> Bool -> VariableInitialization GIdentifier (Typed loc) -> ExprM m ()
varInit2Prover l isConst True (VariableInitialization _ v@(VarName vl (VIden n)) _ e) = do
    ie <- mapM expr2Prover e
    addVar n (ie,Just $ typed vl)
varInit2Prover l isConst False (VariableInitialization _ v@(VarName vl (VIden n)) _ (Just e)) = do
    ie <- expr2Prover e
    addVar n (Just ie,Just $ typed vl)
varInit2Prover l isConst isHavoc vd = lift $ do
    pp1 <- pp isConst
    pp2 <- pp isHavoc
    pp3 <- pp vd
    genTcError (locpos l) False $ text "failed to convert variable initialization to core" <+> pp1 <+> pp2 <+> pp3

expr2ProverMb :: (ProverK loc m) => Expression GIdentifier (Typed loc) -> ExprM m (Maybe IExpr)
expr2ProverMb (RVariablePExpr l v@(VarName tl (VIden n))) = do
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
    IIdx (VarName _ (VIden v)) <- expr2Prover lhs
    ie <- expr2Prover e
    addVar v (Just ie,Nothing)
    return Nothing
expr2ProverMb (VArraySizeExpr l e) = do
    let p = unTyped l
    sz <- lift $ typeSize p (typed $ loc e)
    expr2ProverMb $ fmap (Typed p) sz
expr2ProverMb e@(isInlinableExpr -> True) = do
    let Typed l t = loc e
    mb <- lift $ runSimplify $ tryInlineExpr l $ fmap typed e
    case mb of
        Just e' -> expr2ProverMb $ fmap (Typed l) e'
        Nothing -> proverProcError "inlinable" t e
expr2ProverMb e@(BuiltinExpr l n args) = builtin2Prover (unTyped l) n args
expr2ProverMb e@(QualExpr l e1 t) = expr2ProverMb e1
expr2ProverMb e = lift $ do
    ppe <- ppExprTy (fmap typed e)
    genTcError (locpos $ unTyped $ loc e) True $ text "failed to convert expression" <+> ppe <+> text "to prover expression"
    
proverProcError str (DecT (DVar v)) e = do
    lift $ addGDependencies $ VIden v
    lift $ do
        ppe <- ppExprTy (fmap typed e)
        tcError (locpos $ unTyped $ loc e) $ Halt $ GenTcError (text "failed to convert" <+> text str <+> text "expression" <+> ppe <+> text "to prover expression") Nothing
proverProcError str t e = do
    lift $ do
        ppe <- ppExprTy (fmap typed e)
        ppt <- pp t
        genTcError (locpos $ unTyped $ loc e) True $ text "failed to convert" <+> text str <+> text "expression" <+> ppe <+> text "to prover expression: unknown declaration type" <+> ppt

variadicExpr2Prover :: (ProverK loc m) => (Expression GIdentifier (Typed loc),IsVariadic) -> ExprM m IExpr
variadicExpr2Prover (e,False) = expr2Prover e
variadicExpr2Prover (e,True) = lift $ do
    ppe <- pp e
    genTcError (locpos $ unTyped $ loc e) True $ text "failed to convert variadic expression" <+> ppe <+> text "to prover expression"
    
expr2Prover :: (ProverK loc m) => Expression GIdentifier (Typed loc) -> ExprM m IExpr
expr2Prover e = do
    mb <- expr2ProverMb e
    case mb of
        Nothing -> lift $ do
            ppe <- pp e
            genTcError (locpos $ unTyped $ loc e) False $ text "failed to convert void expression" <+> ppe <+> text "to prover expression"
        Just e' -> return e'
    
lit2Prover :: (ProverK loc m) => Literal (Typed loc) -> ExprM m IExpr
lit2Prover lit = do
    let Typed l t = loc lit
    mplus
        (lift (typeToBaseType l t) >>= litVal2Prover (fmap unTyped lit))
        (lift (typeToComplexType l t) >>= litArr2Prover (fmap unTyped lit))

litVal2Prover :: ProverK loc m => Literal loc -> BaseType -> ExprM m IExpr
litVal2Prover lit@(IntLit l i) (TyPrim t) = case t of
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
    otherwise -> lift $ do
        pp1 <- pp lit
        genTcError (locpos l) False $ text "failed to convert literal" <+> pp1 <+> text "to prover value"
litVal2Prover lit@(FloatLit l f) (TyPrim t) = case t of
    DatatypeFloat32 _ -> return $ ILit $ IFloat32 $ realToFrac f
    DatatypeFloat64 _ -> return $ ILit $ IFloat64 $ realToFrac f
    otherwise -> lift $ do
        pp1 <- pp lit
        genTcError (locpos l) False $ text "failed to convert literal" <+> pp1 <+> text "to prover value"
litVal2Prover lit@(StringLit l s) (TyPrim t) = case t of
    otherwise -> lift $ do
        pp1 <- pp lit
        genTcError (locpos l) False $ text "failed to convert literal" <+> pp1 <+> text "to prover value"
litVal2Prover lit@(BoolLit l b) (TyPrim t) = case t of
    DatatypeBool _ -> return $ ILit $ IBool b
    otherwise -> lift $ do
        pp1 <- pp lit
        genTcError (locpos l) False $ text "failed to convert literal" <+> pp1 <+> text "to prover value"
litVal2Prover lit t = lift $ do
    pp1 <- pp lit
    pp2 <- pp t
    genTcError (locpos $ loc lit) False $ text "failed to convert literal" <+> pp1 <> text "::" <> pp2 <+> text "to prover value"

litArr2Prover :: ProverK loc m => Literal loc -> ComplexType -> ExprM m IExpr
litArr2Prover lit t = lift $ do
    pp1 <- pp lit
    pp2 <- pp t
    genTcError (locpos $ loc lit) False $ text "failed to convert literal" <+> pp1 <> text "::" <> pp2 <+> text "to prover array"

