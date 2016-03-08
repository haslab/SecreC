{-# LANGUAGE DeriveDataTypeable, ViewPatterns, FlexibleContexts, GADTs #-}

-- Static semantics, used by the typechecker to evaluate indexes
module Language.SecreC.TypeChecker.Semantics (
      tryEvaluateIndexExpr
    , evaluateIndexExpr
    , tryEvaluateBoolExpr
    , evaluateBoolExpr
    , simplifyIndexExpr
    , evaluateExpr
    , tryResolveEVar
    , evaluateTypeSize
    , evaluateTypeDim
    ) where

import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.TypeChecker.Base
import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import {-# SOURCE #-} Language.SecreC.TypeChecker.Index

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

evaluateTypeSize :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Word64
evaluateTypeSize l t = evaluate l (pp t) $ evalTypeSize l t

evaluateTypeDim :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Word64
evaluateTypeDim l t = evaluate l (pp t) $ evalTypeDim l t

tryEvaluateIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either SecrecError Word64)
tryEvaluateIndexExpr e = evaluate (unTyped $ loc e) (pp e) $ tryEvalIndexExpr e

evaluateIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m Word64
evaluateIndexExpr e = evaluate (unTyped $ loc e) (pp e) $ evalIndexExpr e

tryEvaluateBoolExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either SecrecError Bool)
tryEvaluateBoolExpr e = evaluate (unTyped $ loc e) (pp e) $ tryEvalBoolExpr e

evaluateBoolExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m Bool
evaluateBoolExpr e = evaluate (unTyped $ loc e) (pp e) $ evalBoolExpr e

simplifyIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Expression VarIdentifier (Typed loc))
simplifyIndexExpr e = evaluate (unTyped $ loc e) (pp e) $ simplIndexExpr e

evaluateExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m HsVal
evaluateExpr e = evaluate (unTyped $ loc e) (pp e) $ evalExpr e

-- * Internal declarations

evaluate :: (MonadIO m,MonadBaseControl IO m,Location loc) => loc -> Doc -> TcM loc m a -> TcM loc m a
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
        
tryEvalIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either SecrecError Word64)
tryEvalIndexExpr e = (liftM Right $ evalIndexExpr e) `catchError` (return . Left)

evalIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m Word64
evalIndexExpr e = do
    v <- evalExpr e
    case v of
        HsUint64 x -> return x
        HsLit (IntLit _ x) -> return $ fromInteger x
        otherwise -> genTcError (locpos $ loc e) (pp v <+> text "not an index")

tryEvalBoolExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either SecrecError Bool)
tryEvalBoolExpr e = (liftM Right $ evalBoolExpr e) `catchError` (return . Left)

evalBoolExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m Bool
evalBoolExpr e = do
    v <- evalExpr e
    case v of
        HsLit (BoolLit _ x) -> return x
        otherwise -> genTcError (locpos $ loc e) (pp v <+> text "not a boolean")

simplIndexExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Expression VarIdentifier (Typed loc))
simplIndexExpr e = do
    let l = unTyped $ loc e
    let ty = Typed l $ BaseT index
    mb <- tryEvalIndexExpr e
    case mb of
        Left err -> return e
        Right i -> return $ LitPExpr ty $ IntLit ty $ toInteger i

evalExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m HsVal
evalExpr e@(BinaryAssign l e1 o e2) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(QualExpr l e1 t) = evalExpr (updLoc e1 (flip Typed (typed $ loc $ fst t) $ unTyped $ loc e1))
evalExpr e@(CondExpr l c e1 e2) = genTcError (locpos l) (pp e)
evalExpr e@(BinaryExpr l e1 o e2) = do
    d <- typeToDecType (unTyped l) (typed $ loc o)
    evalProc (unTyped l) d [(e1,False),(e2,False)]
evalExpr e@(PreOp l _ e1) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(PostOp l _ e1) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(UnaryExpr l o e1) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(DomainIdExpr l e1) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(StringFromBytesExpr l e1) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(BytesFromStringExpr l e1) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(ProcCallExpr l n _ es) = do
    d <- typeToDecType (unTyped l) (typed $ loc n)
    evalProc (unTyped l) d es
evalExpr e@(PostIndexExpr l e1 s) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(SelectionExpr l e1 a) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(ArrayConstructorPExpr l es) = genTcError (locpos l) (pp e) -- TODO
evalExpr e@(RVariablePExpr l v) = evalVarName v
evalExpr e@(LitPExpr l lit) = evalLit lit

evalVarName :: (VarsIdTcM loc m,Location loc) => VarName VarIdentifier (Typed loc) -> TcM loc m HsVal
evalVarName v = do
    let l = unTyped $ loc v
    mb <- tryResolveEVar l (varNameId v) (typed $ loc v)
    case mb of
        Nothing -> do
            tcError (locpos l) $ UnresolvedVariable (pp v)
        Just e' -> evalExpr e'

evalProc :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> [(Expression VarIdentifier (Typed loc),IsVariadic)] -> TcM loc m HsVal
evalProc l (DVar v) args = do
    d <- resolveDVar l v
    evalProc l d args
evalProc l (DecType _ _ [] d1 d2 [] _ proc) args = tcBlock $ do
    addHeadTDict $ fmap (updpos l) d1
    addHeadTDict $ fmap (updpos l) d2
    evalProc l proc args
evalProc l (ProcType _ n vars ret stmts) args = tcBlock $ do
    if (length vars == length args)
        then do
            mapM evalProcParam (zip (List.map (\(x,y,z) -> (x,unCond y,z)) vars) args)
            evalStmts $ List.map (fmap (fmap (updpos l))) stmts
        else genTcError (locpos l) (text "invalid number of procedure arguments")
  where
    evalProcParam ((isConst,v@(VarName t n),False),(arg,False)) = do
        addVar LocalScope n isConst (EntryEnv l t)
        unifiesExprTy l (varExpr v) (fmap typed arg)
evalProc l t args = genTcError (locpos l) (text "can't evaluate procedure" <+> pp t <+> parens (sepBy comma $ List.map pp args))

evalStmts :: (VarsIdTcM loc m,Location loc) => [Statement VarIdentifier (Typed loc)] -> TcM loc m HsVal
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

evalStmt :: (VarsIdTcM loc m,Location loc) => Statement VarIdentifier (Typed loc) -> TcM loc m HsVal
evalStmt (CompoundStatement _ ss) = tcBlock $ evalStmts ss
evalStmt (IfStatement _ c s1 s2) = do
    HsLit (BoolLit _ ok) <- evalExpr c
    if ok
        then evalStmt s1
        else maybe (return HsVoid) evalStmt s2
evalStmt (ForStatement _ fi c inc s) = tcBlock $ do
    evalForInit fi
    let cyc = do
        HsLit (BoolLit _ ok) <- maybe (return $ HsLit $ BoolLit () True) evalExpr c
        if ok then evalStmt s `loopCont` (mapM evalExpr inc >> cyc) else return HsVoid
    cyc
  where
    evalForInit (InitializerExpression e) = mapM_ evalExpr e
    evalForInit (InitializerVariable d) = evalVarDecl d
evalStmt (WhileStatement _ c s) = tcBlock $ do
    let cyc = do
        HsLit (BoolLit _ ok) <- evalExpr c
        if ok then evalStmt s `loopCont` cyc else return HsVoid
    cyc
evalStmt s@(PrintStatement l es) = genTcError (locpos l) (pp s)
evalStmt (DowhileStatement _ s c) = do
    let cyc = do
        evalStmt s `loopCont` do { HsLit (BoolLit _ ok) <- evalExpr c; if ok then cyc else return HsVoid }
    cyc
evalStmt (AssertStatement l e) = do
    HsLit (BoolLit _ ok) <- evalExpr e
    if ok then return HsVoid else genTcError (locpos l) (text "Assert failure:" <+> pp e)
evalStmt s@(SyscallStatement l n ps) = do
    case (n,ps) of
        (stripPrefix "haskell." -> Just hsn,ps) -> do
            (args,ret) <- parseHaskellParams ps
            res <- haskellSyscall (unTyped l) hsn args
            val <- hsValToSExpr (unTyped l) res
            let Typed lret tret = loc ret
            addVar LocalScope (varNameId ret) False (EntryEnv lret tret) 
            unifiesExprTy (unTyped l) (fmap typed $ varExpr ret) (fmap typed val)
            return HsVoid
        ("core.size",[SyscallPush _ e,SyscallReturn _ ret]) -> do
            let t = typed $ loc e
            i <- evalTypeSize (unTyped l) t
            return $ HsUint64 i
        otherwise -> genTcError (locpos l) (pp s)
  where
    parseHaskellParams [SyscallReturn _ ret] = return ([],ret)
    parseHaskellParams (SyscallPush _ e:ps) = do
        v <- evalExpr e
        (vs,ret) <- parseHaskellParams ps
        return (v:vs,ret) 
    parseHaskellParams _ = genTcError (locpos l) (text "invalid haskell parameters for " <+> pp s)
evalStmt (VarStatement _ d) = evalVarDecl d >> return HsVoid
evalStmt (ReturnStatement _ Nothing) = return HsVoid
evalStmt (ReturnStatement _ (Just e)) = evalExpr e
evalStmt (ContinueStatement _) = return HsContinue
evalStmt (BreakStatement _) = return HsBreak
evalStmt (ExpressionStatement _ e) = do
    evalExpr e
    return HsVoid

evalTypeSize :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Word64
evalTypeSize l t = do
    sz <- typeSize l t
    evalIndexExpr $ fmap (Typed l) sz

evalTypeDim :: (VarsIdTcM loc m,Location loc) => loc -> Type -> TcM loc m Word64
evalTypeDim l t = do
    sz <- typeDim l t
    evalIndexExpr $ fmap (Typed l) sz

evalVarDecl :: (VarsIdTcM loc m,Location loc) => VariableDeclaration VarIdentifier (Typed loc) -> TcM loc m ()
evalVarDecl (VariableDeclaration _ t is) = mapM_ (evalVarInit $ typed $ loc t) is

evalVarInit :: (VarsIdTcM loc m,Location loc) => Type -> VariableInitialization VarIdentifier (Typed loc) -> TcM loc m ()
evalVarInit t (VariableInitialization l n _ e) = do
    addVar LocalScope (varNameId n) False (EntryEnv (unTyped l) t)
    case e of
        Nothing -> return ()
        Just x -> unifiesExprTy (unTyped l) (fmap typed $ varExpr n) (fmap typed x)

evalConstDecl :: (VarsIdTcM loc m,Location loc) => ConstDeclaration VarIdentifier (Typed loc) -> TcM loc m ()
evalConstDecl (ConstDeclaration _ t is) = mapM_ (evalConstInit $ typed $ loc t) is

evalConstInit :: (VarsIdTcM loc m,Location loc) => Type -> ConstInitialization VarIdentifier (Typed loc) -> TcM loc m ()
evalConstInit t (ConstInitialization l n _ e) = do
    addVar LocalScope (varNameId n) True (EntryEnv (unTyped l) t)
    case e of
        Nothing -> return ()
        Just x -> unifiesExprTy (unTyped l) (fmap typed $ varExpr n) (fmap typed x)

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
evalLit l = return $ HsLit $ funit l

isHsInt8 :: HsVal -> Maybe Int8
isHsInt8 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsInt8 (HsInt8 i) = Just i

isHsInt16 :: HsVal -> Maybe Int16
isHsInt16 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsInt16 (HsInt16 i) = Just i

isHsInt32 :: HsVal -> Maybe Int32
isHsInt32 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsInt32 (HsInt32 i) = Just i

isHsInt64 :: HsVal -> Maybe Int64
isHsInt64 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsInt64 (HsInt64 i) = Just i

isHsUint8 :: HsVal -> Maybe Word8
isHsUint8 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsUint8 (HsUint8 i) = Just i

isHsUint16 :: HsVal -> Maybe Word16
isHsUint16 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsUint16 (HsUint16 i) = Just i

isHsUint32 :: HsVal -> Maybe Word32
isHsUint32 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsUint32 (HsUint32 i) = Just i

isHsUint64 :: HsVal -> Maybe Word64
isHsUint64 (HsLit (IntLit _ i)) = Just $ fromInteger i
isHsUint64 (HsUint64 i) = Just i

isHsFloat32 :: HsVal -> Maybe Float
isHsFloat32 (HsLit (FloatLit _ i)) = Just $ realToFrac i
isHsFloat32 (HsFloat32 i) = Just i

isHsFloat64 :: HsVal -> Maybe Double
isHsFloat64 (HsLit (FloatLit _ i)) = Just $ realToFrac i
isHsFloat64 (HsFloat64 i) = Just i

-- | Built-in system calls to haskell
haskellSyscall :: (VarsIdTcM loc m,Location loc) => loc -> String -> [HsVal] -> TcM loc m HsVal
haskellSyscall l "sub_int8" [isHsInt8 -> Just i1,isHsInt8 -> Just i2] = return $ HsInt8 (i1 - i2)
haskellSyscall l "sub_int16" [isHsInt16 -> Just i1,isHsInt16 -> Just i2] = return $ HsInt16 (i1 - i2)
haskellSyscall l "sub_int32" [isHsInt32 -> Just i1,isHsInt32 -> Just i2] = return $ HsInt32 (i1 - i2)
haskellSyscall l "sub_int64" [isHsInt64 -> Just i1,isHsInt64 -> Just i2] = return $ HsInt64 (i1 - i2)
haskellSyscall l "sub_uint8" [isHsUint8 -> Just i1,isHsUint8 -> Just i2] = return $ HsUint8 (i1 - i2)
haskellSyscall l "sub_uint16" [isHsUint16 -> Just i1,isHsUint16 -> Just i2] = return $ HsUint16 (i1 - i2)
haskellSyscall l "sub_uint32" [isHsUint32 -> Just i1,isHsUint32 -> Just i2] = return $ HsUint32 (i1 - i2)
haskellSyscall l "sub_uint64" [isHsUint64 -> Just i1,isHsUint64 -> Just i2] = return $ HsUint64 (i1 - i2)
haskellSyscall l "sub_float32" [isHsFloat32 -> Just i1,isHsFloat32 -> Just i2] = return $ HsFloat32 (i1 - i2)
haskellSyscall l "sub_float64" [isHsFloat64 -> Just i1,isHsFloat64 -> Just i2] = return $ HsFloat64 (i1 - i2)
haskellSyscall l "add_int8" [isHsInt8 -> Just i1,isHsInt8 -> Just i2] = return $ HsInt8 (i1 + i2)
haskellSyscall l "add_int16" [isHsInt16 -> Just i1,isHsInt16 -> Just i2] = return $ HsInt16 (i1 + i2)
haskellSyscall l "add_int32" [isHsInt32 -> Just i1,isHsInt32 -> Just i2] = return $ HsInt32 (i1 + i2)
haskellSyscall l "add_int64" [isHsInt64 -> Just i1,isHsInt64 -> Just i2] = return $ HsInt64 (i1 + i2)
haskellSyscall l "add_uint8" [isHsUint8 -> Just i1,isHsUint8 -> Just i2] = return $ HsUint8 (i1 + i2)
haskellSyscall l "add_uint16" [isHsUint16 -> Just i1,isHsUint16 -> Just i2] = return $ HsUint16 (i1 + i2)
haskellSyscall l "add_uint32" [isHsUint32 -> Just i1,isHsUint32 -> Just i2] = return $ HsUint32 (i1 + i2)
haskellSyscall l "add_uint64" [isHsUint64 -> Just i1,isHsUint64 -> Just i2] = return $ HsUint64 (i1 + i2)
haskellSyscall l "add_float32" [isHsFloat32 -> Just i1,isHsFloat32 -> Just i2] = return $ HsFloat32 (i1 + i2)
haskellSyscall l "add_float64" [isHsFloat64 -> Just i1,isHsFloat64 -> Just i2] = return $ HsFloat64 (i1 + i2)
haskellSyscall l "mul_int8" [isHsInt8 -> Just i1,isHsInt8 -> Just i2] = return $ HsInt8 (i1 * i2)
haskellSyscall l "mul_int16" [isHsInt16 -> Just i1,isHsInt16 -> Just i2] = return $ HsInt16 (i1 * i2)
haskellSyscall l "mul_int32" [isHsInt32 -> Just i1,isHsInt32 -> Just i2] = return $ HsInt32 (i1 * i2)
haskellSyscall l "mul_int64" [isHsInt64 -> Just i1,isHsInt64 -> Just i2] = return $ HsInt64 (i1 * i2)
haskellSyscall l "mul_uint8" [isHsUint8 -> Just i1,isHsUint8 -> Just i2] = return $ HsUint8 (i1 * i2)
haskellSyscall l "mul_uint16" [isHsUint16 -> Just i1,isHsUint16 -> Just i2] = return $ HsUint16 (i1 * i2)
haskellSyscall l "mul_uint32" [isHsUint32 -> Just i1,isHsUint32 -> Just i2] = return $ HsUint32 (i1 * i2)
haskellSyscall l "mul_uint64" [isHsUint64 -> Just i1,isHsUint64 -> Just i2] = return $ HsUint64 (i1 * i2)
haskellSyscall l "mul_float32" [isHsFloat32 -> Just i1,isHsFloat32 -> Just i2] = return $ HsFloat32 (i1 * i2)
haskellSyscall l "mul_float64" [isHsFloat64 -> Just i1,isHsFloat64 -> Just i2] = return $ HsFloat64 (i1 * i2)
haskellSyscall l str args = genTcError (locpos l) $ text (show str) <+> parens (sepBy comma (List.map pp args))

hsValToSExpr :: (MonadIO m,Location loc) => loc -> HsVal -> TcM loc m (SExpr VarIdentifier (Typed loc))
hsValToSExpr l v = do
    e <- hsValToExpr l v
    return (e)

hsValToExpr :: (MonadIO m,Location loc) => loc -> HsVal -> TcM loc m (Expression VarIdentifier (Typed loc))
hsValToExpr l (HsInt8 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int8)
hsValToExpr l (HsInt16 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int16)
hsValToExpr l (HsInt32 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int32)
hsValToExpr l (HsInt64 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT int64)
hsValToExpr l (HsUint8 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT uint8)
hsValToExpr l (HsUint16 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT uint16)
hsValToExpr l (HsUint32 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT uint32)
hsValToExpr l (HsUint64 i) = return $ LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l $ BaseT uint64)
hsValToExpr l (HsFloat32 i) = return $ LitPExpr t $ FloatLit t $ realToFrac i
    where t = (Typed l $ BaseT float32)
hsValToExpr l (HsFloat64 i) = return $ LitPExpr t $ FloatLit t $ realToFrac i
    where t = (Typed l $ BaseT float64)
hsValToExpr l (HsLit lit) = return $ LitPExpr t $ fmap (const t) lit
    where t = (Typed l $ ComplexT $ TyLit lit)
hsValToExpr l v = genTcError (locpos l) $ text "Cannot convert Haskell value" <+> quotes (pp v) <+> text "to an expression."



data HsVal where
    HsInt8 :: Int8 -> HsVal
    HsInt16 :: Int16 -> HsVal
    HsInt32 :: Int32 -> HsVal
    HsInt64 :: Int64 -> HsVal
    HsUint8 :: Word8 -> HsVal
    HsUint16 :: Word16 -> HsVal
    HsUint32 :: Word32 -> HsVal
    HsUint64 :: Word64 -> HsVal
    HsFloat32 :: Float -> HsVal
    HsFloat64 :: Double -> HsVal
    HsLit :: Literal () -> HsVal
    HsContinue :: HsVal
    HsBreak :: HsVal
    HsVoid :: HsVal
    HsSysPush :: HsVal -> HsVal
    HsSysRet :: HsVal -> HsVal
    HsSysRef :: HsVal -> HsVal
    HsSysCRef :: HsVal -> HsVal
  deriving (Data,Typeable,Show)

--instance Monad m => Vars m HsVal where
--    traverseVars f h = return h

instance PP HsVal where
    pp (HsInt8 i) = text (show i)
    pp (HsInt16 i) = text (show i)
    pp (HsInt32 i) = text (show i)
    pp (HsInt64 i) = text (show i)
    pp (HsUint8 i) = text (show i)
    pp (HsUint16 i) = text (show i)
    pp (HsUint32 i) = text (show i)
    pp (HsUint64 i) = text (show i)
    pp (HsFloat32 i) = text (show i)
    pp (HsFloat64 i) = text (show i)
    pp (HsLit l) = pp l
    pp HsContinue = text "continue"
    pp HsBreak = text "break"
    pp HsVoid = text "void"
    pp (HsSysPush v) = pp v 
    pp (HsSysRet v) = text "__ret" <+> pp v
    pp (HsSysRef v) = text "__ref" <+> pp v
    pp (HsSysCRef v) = text "__cref" <+> pp v

instance Eq HsVal where
    (HsInt8 i1) == (HsInt8 i2) = i1 == i2
    (HsInt8 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt8 i2) = i1 == toInteger i2
    (HsInt16 i1) == (HsInt16 i2) = i1 == i2
    (HsInt16 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt16 i2) = i1 == toInteger i2
    (HsInt32 i1) == (HsInt32 i2) = i1 == i2
    (HsInt32 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt32 i2) = i1 == toInteger i2
    (HsInt64 i1) == (HsInt64 i2) = i1 == i2
    (HsInt64 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt64 i2) = i1 == toInteger i2
    (HsLit l1) == (HsLit l2) = l1 == l2
    (HsUint8 i1) == (HsUint8 i2) = i1 == i2
    (HsUint8 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint8 i2) = i1 == toInteger i2
    (HsUint16 i1) == (HsUint16 i2) = i1 == i2
    (HsUint16 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint16 i2) = i1 == toInteger i2
    (HsUint32 i1) == (HsUint32 i2) = i1 == i2
    (HsUint32 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint32 i2) = i1 == toInteger i2
    (HsUint64 i1) == (HsUint64 i2) = i1 == i2
    (HsUint64 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint64 i2) = i1 == toInteger i2
    (HsFloat32 i1) == (HsFloat32 i2) = i1 == i2
    (HsFloat32 i1) == (HsLit (FloatLit _ i2)) = realToFrac i1 == i2
    (HsLit (FloatLit _ i1)) == (HsFloat32 i2) = i1 == realToFrac i2
    (HsFloat64 i1) == (HsFloat64 i2) = i1 == i2
    (HsFloat64 i1) == (HsLit (FloatLit _ i2)) = realToFrac i1 == i2
    (HsLit (FloatLit _ i1)) == (HsFloat64 i2) = i1 == realToFrac i2
    HsContinue == HsContinue = True
    HsBreak == HsBreak = True
    HsVoid == HsVoid = True
    (HsSysPush v1) == (HsSysPush v2) = v1 == v2
    (HsSysRet v1) == (HsSysRet v2) = v1 == v2
    (HsSysRef v1) == (HsSysRef v2) = v1 == v2
    (HsSysCRef v1) == (HsSysCRef v2) = v1 == v2
    v1 == v2 = False

instance Ord HsVal where
    compare (HsInt8 i1) (HsInt8 i2) = i1 `compare` i2
    compare (HsInt8 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt8 i2) = i1 `compare` toInteger i2
    compare (HsInt16 i1) (HsInt16 i2) = i1 `compare` i2
    compare (HsInt16 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt16 i2) = i1 `compare` toInteger i2
    compare (HsInt32 i1) (HsInt32 i2) = i1 `compare` i2
    compare (HsInt32 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt32 i2) = i1 `compare` toInteger i2
    compare (HsInt64 i1) (HsInt64 i2) = i1 `compare` i2
    compare (HsInt64 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt64 i2) = i1 `compare` toInteger i2
    compare (HsLit l1) (HsLit l2) = l1 `compare` l2
    compare (HsUint8 i1) (HsUint8 i2) = i1 `compare` i2
    compare (HsUint8 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint8 i2) = i1 `compare` toInteger i2
    compare (HsUint16 i1) (HsUint16 i2) = i1 `compare` i2
    compare (HsUint16 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint16 i2) = i1 `compare` toInteger i2
    compare (HsUint32 i1) (HsUint32 i2) = i1 `compare` i2
    compare (HsUint32 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint32 i2) = i1 `compare` toInteger i2
    compare (HsUint64 i1) (HsUint64 i2) = i1 `compare` i2
    compare (HsUint64 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint64 i2) = i1 `compare` toInteger i2
    compare (HsFloat32 i1) (HsFloat32 i2) = i1 `compare` i2
    compare (HsFloat32 i1) (HsLit (FloatLit _ i2)) = realToFrac i1 `compare` i2
    compare (HsLit (FloatLit _ i1)) (HsFloat32 i2) = i1 `compare` realToFrac i2
    compare (HsFloat64 i1) (HsFloat64 i2) = i1 `compare` i2
    compare (HsFloat64 i1) (HsLit (FloatLit _ i2)) = realToFrac i1 `compare` i2
    compare (HsLit (FloatLit _ i1)) (HsFloat64 i2) = i1 `compare` realToFrac i2
    compare HsContinue HsContinue = EQ
    compare HsBreak HsBreak = EQ
    compare HsVoid HsVoid = EQ
    compare (HsSysPush v1) (HsSysPush v2) = v1 `compare` v2
    compare (HsSysRet v1) (HsSysRet v2) = v1 `compare` v2
    compare (HsSysRef v1) (HsSysRef v2) = v1 `compare` v2
    compare (HsSysCRef v1) (HsSysCRef v2) = v1 `compare` v2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)