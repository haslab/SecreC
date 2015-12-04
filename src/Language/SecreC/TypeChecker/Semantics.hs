{-# LANGUAGE GADTs #-}

-- Static semantics, used by the typechecker to evaluate indexes
module Language.SecreC.TypeChecker.Semantics where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Environment

import Data.Int
import Data.Word
import Data.Map as Map
import Data.Maybe
import Data.List as List

import Text.PrettyPrint

import Control.Monad
import Control.Monad.State as State
import Control.Monad.Except

tryEvalIndexExpr :: (Vars loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc (Either SecrecError Word64)
tryEvalIndexExpr e = (liftM Right $ evalIndexExpr e) `catchError` (return . Left)

evalIndexExpr :: (Vars loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc Word64
evalIndexExpr e = do
    v <- evalExpr e
    case v of
        HsUint64 x -> return x
        HsLit (IntLit _ x) -> return $ fromInteger x
        otherwise -> tcError (locpos $ loc e) $ StaticEvalError (text (show v) <+> text "not an index")

simplifyIndexExpr :: (Vars loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc (Expression VarIdentifier (Typed loc))
simplifyIndexExpr e = do
    let l = unTyped $ loc e
    let ty = Typed l $ BaseT index
    mb <- tryEvalIndexExpr e
    case mb of
        Left err -> return e
        Right i -> return $ LitPExpr ty $ IntLit ty $ toInteger i

evalExpr :: (Vars loc,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc HsVal
evalExpr e@(BinaryAssign l e1 o e2) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(QualExpr l e1 t) = evalExpr (updLoc e1 (flip Typed (typed $ loc t) $ unTyped $ loc e1))
evalExpr e@(CondExpr l c e1 e2) = tcError (locpos l) $ StaticEvalError (pp e)
evalExpr e@(BinaryExpr l e1 o e2) = evalProc (unTyped l) (typed $ loc o) [e1,e2]
evalExpr e@(CastExpr l t e1) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(PreOp l _ e1) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(PostOp l _ e1) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(UnaryExpr l o e1) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(DomainIdExpr l e1) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(StringFromBytesExpr l e1) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(BytesFromStringExpr l e1) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(ProcCallExpr l n es) = evalProc (unTyped l) (typed $ loc n) es
evalExpr e@(PostIndexExpr l e1 s) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(SelectionExpr l e1 a) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(ArrayConstructorPExpr l es) = tcError (locpos l) $ StaticEvalError (pp e) -- TODO
evalExpr e@(RVariablePExpr l v) = evalVarName v
evalExpr e@(LitPExpr l lit) = evalLit lit

evalVarName :: (Vars loc,Location loc) => VarName VarIdentifier (Typed loc) -> TcM loc HsVal
evalVarName v = do
    let l = unTyped $ loc v
    mb <- tryResolveEVar l v
    case mb of
        Nothing -> tcError (locpos l) $ StaticEvalError (pp v)
        Just e' -> evalExpr e'

evalProc :: (Vars loc,Location loc) => loc -> Type -> [Expression VarIdentifier (Typed loc)] -> TcM loc HsVal
evalProc l (DecT (ProcType _ _ vars ret stmts)) args = tcBlock $ do
    if (length vars == length args)
        then do
            mapM evalProcParam (zip vars args)
            evalStmts $ List.map (fmap (fmap (updpos l))) stmts
        else tcError (locpos l) $ StaticEvalError (text "invalid number of procedure arguments")
  where
    evalProcParam (VarName t n,arg) = addVar LocalScope n (EntryEnv l t $ KnownExpression arg)
evalProc l t args = tcError (locpos l) $ StaticEvalError (text "can't evaluate procedure")

evalStmts :: (Vars loc,Location loc) => [Statement VarIdentifier (Typed loc)] -> TcM loc HsVal
evalStmts [] = return HsVoid
evalStmts [s] = evalStmt s
evalStmts (s:ss) = do
    v <- evalStmt s
    case v of
        HsContinue -> return v
        HsBreak -> return v
        otherwise -> evalStmts ss

loopCont m cyc = do
    v <- m
    case v of
        HsContinue -> cyc
        HsBreak -> return HsVoid
        otherwise -> cyc

evalStmt :: (Vars loc,Location loc) => Statement VarIdentifier (Typed loc) -> TcM loc HsVal
evalStmt (CompoundStatement _ ss) = tcBlock $ evalStmts ss
evalStmt (IfStatement _ c s1 s2) = do
    HsBool ok <- evalExpr c
    if ok
        then evalStmt s1
        else maybe (return HsVoid) evalStmt s2
evalStmt (ForStatement _ fi c inc s) = tcBlock $ do
    evalForInit fi
    let cyc = do
        HsBool ok <- maybe (return $ HsBool True) evalExpr c
        if ok then evalStmt s `loopCont` (mapM evalExpr inc >> cyc) else return HsVoid
    cyc
  where
    evalForInit (InitializerExpression e) = mapM_ evalExpr e
    evalForInit (InitializerVariable d) = evalVarDecl d
evalStmt (WhileStatement _ c s) = tcBlock $ do
    let cyc = do
        HsBool ok <- evalExpr c
        if ok then evalStmt s `loopCont` cyc else return HsVoid
    cyc
evalStmt s@(PrintStatement l es) = tcError (locpos l) $ StaticEvalError (pp s)
evalStmt (DowhileStatement _ s c) = do
    let cyc = do
        evalStmt s `loopCont` do { HsBool ok <- evalExpr c; if ok then cyc else return HsVoid }
    cyc
evalStmt (AssertStatement l e) = do
    HsBool ok <- evalExpr e
    if ok then return HsVoid else tcError (locpos l) $ StaticEvalError (text "Assert failure:" <+> pp e)
evalStmt s@(SyscallStatement l n ps) = do
    case stripPrefix "haskell." n of
        Just hsn -> do
            (args,ret) <- parseHaskellParams ps
            res <- haskellSyscall (unTyped l) hsn args
            let val = KnownExpression $ hsValToExpr (unTyped l) res
            addVar LocalScope (varNameId ret) (EntryEnv (unTyped $ loc ret) (typed $ loc ret) val) 
            return HsVoid
        Nothing -> tcError (locpos l) $ StaticEvalError (pp s)
  where
    parseHaskellParams [SyscallReturn _ ret] = return ([],ret)
    parseHaskellParams (SyscallPush _ e:ps) = do
        v <- evalExpr e
        (vs,ret) <- parseHaskellParams ps
        return (v:vs,ret) 
    parseHaskellParams _ = tcError (locpos l) $ StaticEvalError (text "invalid haskell parameters for " <+> pp s)

evalStmt (VarStatement _ d) = evalVarDecl d >> return HsVoid
evalStmt (ReturnStatement _ Nothing) = return HsVoid
evalStmt (ReturnStatement _ (Just e)) = evalExpr e
evalStmt (ContinueStatement _) = return HsContinue
evalStmt (BreakStatement _) = return HsBreak
evalStmt (ExpressionStatement _ e) = do
    evalExpr e
    return HsVoid

evalVarDecl :: (Vars loc,Location loc) => VariableDeclaration VarIdentifier (Typed loc) -> TcM loc ()
evalVarDecl (VariableDeclaration (Typed l t) _ is) = mapM_ (evalVarInit t) is

evalVarInit :: (Vars loc,Location loc) => Type -> VariableInitialization VarIdentifier (Typed loc) -> TcM loc ()
evalVarInit t (VariableInitialization l n _ e) = do
    let v = case e of
            Nothing -> NoValue
            Just ex -> KnownExpression ex
    addVar LocalScope (varNameId n) (EntryEnv (unTyped l) t v)

add_int8 (HsInt8 i1) (HsInt8 i2) = HsInt8 (i1 + i2)
add_int16 (HsInt16 i1) (HsInt16 i2) = HsInt16 (i1 + i2)
add_int32 (HsInt32 i1) (HsInt32 i2) = HsInt32 (i1 + i2)
add_int64 (HsInt64 i1) (HsInt64 i2) = HsInt64 (i1 + i2)
add_uint8 (HsUint8 i1) (HsUint8 i2) = HsUint8 (i1 + i2)
add_uint16 (HsUint16 i1) (HsUint16 i2) = HsUint16 (i1 + i2)
add_uint32 (HsUint32 i1) (HsUint32 i2) = HsUint32 (i1 + i2)
add_uint64 (HsUint64 i1) (HsUint64 i2) = HsUint64 (i1 + i2)
add_float32 (HsFloat32 i1) (HsFloat32 i2) = HsFloat32 (i1 + i2)
add_float64 (HsFloat64 i1) (HsFloat64 i2) = HsFloat64 (i1 + i2)


evalLit :: (Monad m,Location loc) => Literal loc -> m HsVal
evalLit l = return $ HsLit $ fmap (const ()) l

-- | Built-in system calls to haskell
haskellSyscall :: (Vars loc,Location loc) => loc -> String -> [HsVal] -> TcM loc HsVal
haskellSyscall l "sub_int8" [HsInt8 i1,HsInt8 i2] = return $ HsInt8 (i1 - i2)
haskellSyscall l "sub_int16" [HsInt16 i1,HsInt16 i2] = return $ HsInt16 (i1 - i2)
haskellSyscall l "sub_int32" [HsInt32 i1,HsInt32 i2] = return $ HsInt32 (i1 - i2)
haskellSyscall l "sub_int64" [HsInt64 i1,HsInt64 i2] = return $ HsInt64 (i1 - i2)
haskellSyscall l "sub_uint8" [HsUint8 i1,HsUint8 i2] = return $ HsUint8 (i1 - i2)
haskellSyscall l "sub_uint16" [HsUint16 i1,HsUint16 i2] = return $ HsUint16 (i1 - i2)
haskellSyscall l "sub_uint32" [HsUint32 i1,HsUint32 i2] = return $ HsUint32 (i1 - i2)
haskellSyscall l "sub_uint64" [HsUint64 i1,HsUint64 i2] = return $ HsUint64 (i1 - i2)
haskellSyscall l "sub_float32" [HsFloat32 i1,HsFloat32 i2] = return $ HsFloat32 (i1 - i2)
haskellSyscall l "sub_float64" [HsFloat64 i1,HsFloat64 i2] = return $ HsFloat64 (i1 - i2)
haskellSyscall l "add_int8" [HsInt8 i1,HsInt8 i2] = return $ HsInt8 (i1 + i2)
haskellSyscall l "add_int16" [HsInt16 i1,HsInt16 i2] = return $ HsInt16 (i1 + i2)
haskellSyscall l "add_int32" [HsInt32 i1,HsInt32 i2] = return $ HsInt32 (i1 + i2)
haskellSyscall l "add_int64" [HsInt64 i1,HsInt64 i2] = return $ HsInt64 (i1 + i2)
haskellSyscall l "add_uint8" [HsUint8 i1,HsUint8 i2] = return $ HsUint8 (i1 + i2)
haskellSyscall l "add_uint16" [HsUint16 i1,HsUint16 i2] = return $ HsUint16 (i1 + i2)
haskellSyscall l "add_uint32" [HsUint32 i1,HsUint32 i2] = return $ HsUint32 (i1 + i2)
haskellSyscall l "add_uint64" [HsUint64 i1,HsUint64 i2] = return $ HsUint64 (i1 + i2)
haskellSyscall l "add_float32" [HsFloat32 i1,HsFloat32 i2] = return $ HsFloat32 (i1 + i2)
haskellSyscall l "add_float64" [HsFloat64 i1,HsFloat64 i2] = return $ HsFloat64 (i1 + i2)
haskellSyscall l str args = tcError (locpos l) $ StaticEvalError (pp str <+> hcat (List.map pp args))

tryResolveEVar :: (Vars loc,Location loc) => loc -> VarName VarIdentifier (Typed loc) -> TcM loc (Maybe (Expression VarIdentifier (Typed loc)))
tryResolveEVar l v@(VarName t n) = do
    ss <- liftM (tValues . tDict) State.get
    case Map.lookup (VarName () n) ss of
        Just e -> return (Just e)
        Nothing -> do
            vs <- getVars LocalScope TypeC
            case Map.lookup n vs of
                Nothing -> return Nothing
                Just e -> case entryValue e of
                    UnknownValue -> tcError (locpos l) $ StaticEvalError (pp v)
                    NoValue -> return Nothing
                    KnownExpression e -> return $ Just e

hsValToExpr :: Location loc => loc -> HsVal -> Expression VarIdentifier (Typed loc)
hsValToExpr l (HsInt8 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int8)
hsValToExpr l (HsInt16 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int16)
hsValToExpr l (HsInt32 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int32)
hsValToExpr l (HsInt64 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int64)
hsValToExpr l (HsLit lit) = LitPExpr t $ fmap (const t) lit
    where t = (Typed l $ ComplexT $ TyLit lit)