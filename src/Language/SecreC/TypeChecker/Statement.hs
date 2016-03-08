{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Statement where

import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker.Index

import Data.Bifunctor
import Data.Traversable
import qualified Data.Foldable as Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Int
import Data.Word

import Text.PrettyPrint

import Control.Monad hiding (mapM)
import Control.Monad.IO.Class
import Control.Monad.State as State

import Prelude hiding (mapM)

-- | Left-biased merge of two @StmtClass@es
extendStmtClasses :: Set StmtClass -> Set StmtClass -> Set StmtClass
extendStmtClasses s1 s2 = (Set.filter (not . isStmtFallthru) s1) `Set.union` s2

tcStmts :: (VarsIdTcM loc m,Location loc) => Type -> [Statement Identifier loc] -> TcM loc m ([Statement VarIdentifier (Typed loc)],Type)
tcStmts ret [] = return ([],StmtType $ Set.empty)
tcStmts ret [s] = do
    (s',StmtType c) <- tcAddDeps (loc s) "stmt" $ tcStmt ret s
    return ([s'],StmtType c)
tcStmts ret (s:ss) = do
    (s',StmtType c) <- tcAddDeps (loc s) "stmts" $ tcStmt ret s
    -- if the following statements are never executed, issue an error
    case ss of
        [] -> return ()
        ss -> unless (hasStmtFallthru c) $ tcError (locpos $ loc (head ss)) $ UnreachableDeadCode (vcat $ map pp ss)
    sBvs <- bvs $ bimap mkVarId id s
    ssFvs <- fvs $ map (bimap mkVarId id) ss
    (ss',StmtType cs) <- tcStmts ret ss
    -- issue warning for unused variable declarations
    forSetM_ (sBvs `Set.difference` ssFvs) $ \(v::VarIdentifier) -> tcWarn (locpos $ loc s) $ UnusedVariable (pp v)
    return (s':ss',StmtType $ extendStmtClasses c cs)

-- | Typecheck a non-empty statement
tcNonEmptyStmt :: (VarsIdTcM loc m,Location loc) => Type -> Statement Identifier loc -> TcM loc m (Statement VarIdentifier (Typed loc),Type)
tcNonEmptyStmt ret s = do
    r@(s',StmtType cs) <- tcAddDeps (loc s) "nonempty stmt" $ tcStmt ret s
    when (Set.null cs) $ tcWarn (locpos $ loc s) $ EmptyBranch (pp s)
    return r

-- | Typecheck a statement in the body of a loop
tcLoopBodyStmt :: (VarsIdTcM loc m,Location loc) => Type -> loc -> Statement Identifier loc -> TcM loc m (Statement VarIdentifier (Typed loc),Type)
tcLoopBodyStmt ret l s = do
    (s',StmtType cs) <- tcAddDeps l "loop" $ tcStmt ret s
    -- check that the body can perform more than iteration
    when (Set.null $ Set.filter isIterationStmtClass cs) $ tcWarn (locpos l) $ SingleIterationLoop (pp s)
    -- return the @StmtClass@ for the whole loop
    let t' = StmtType $ Set.insert (StmtFallthru) (Set.filter (not . isLoopStmtClass) cs)
    return (s',t')
    
-- | Typechecks a @Statement@
tcStmt :: (VarsIdTcM loc m,Location loc) => Type -- ^ return type
    -> Statement Identifier loc -- ^ input statement
    -> TcM loc m (Statement VarIdentifier (Typed loc),Type)
tcStmt ret (CompoundStatement l s) = do
    (ss',t) <- tcLocal $ tcStmts ret s
    return (CompoundStatement (Typed l t) ss',t)
tcStmt ret (IfStatement l condE thenS Nothing) = do
    condE' <- tcGuard condE
    (thenS',StmtType cs) <- tcLocal $ tcNonEmptyStmt ret thenS
    -- an if statement falls through if the condition is not satisfied
    let t = StmtType $ Set.insert (StmtFallthru) cs
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' Nothing,t)
tcStmt ret (IfStatement l condE thenS (Just elseS)) = do
    condE' <- tcGuard condE
    (thenS',StmtType cs1) <- tcLocal $ tcNonEmptyStmt ret thenS
    (elseS',StmtType cs2) <- tcLocal $ tcNonEmptyStmt ret elseS 
    let t = StmtType $ cs1 `Set.union` cs2
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' (Just elseS'),t)
tcStmt ret (ForStatement l startE whileE incE bodyS) = tcLocal $ do
    startE' <- tcForInitializer startE
    whileE' <- mapM tcGuard whileE
    incE' <- mapM (tcExpr) incE
    (bodyS',t') <- tcLocal $ tcLoopBodyStmt ret l bodyS
    return (ForStatement (notTyped "tcStmt" l) startE' whileE' incE' bodyS',t')
tcStmt ret (WhileStatement l condE bodyS) = do
    condE' <- tcGuard condE
    (bodyS',t') <- tcLocal $ tcLoopBodyStmt ret l bodyS
    return (WhileStatement (notTyped "tcStmt" l) condE' bodyS',t')
tcStmt ret (PrintStatement (l::loc) argsE) = do
    argsE' <- mapM (tcVariadicArg tcExpr) argsE
    xs <- forM argsE' $ \argE' -> do
        tx <- newTyVar Nothing
        newTypedVar "print" tx $ Just $ ppVariadicArg pp argE'
    tcTopCstrM l $ SupportedPrint (map (mapFst (fmap typed)) argsE') xs
    let exs = map (fmap (Typed l) . varExpr) xs
    let t = StmtType $ Set.singleton $ StmtFallthru
    return (PrintStatement (Typed l t) (zip exs $ map snd argsE'),t)
tcStmt ret (DowhileStatement l bodyS condE) = tcLocal $ do
    (bodyS',t') <- tcLoopBodyStmt ret l bodyS
    condE' <- tcGuard condE
    return (DowhileStatement (notTyped "tcStmt" l) bodyS' condE',t')
tcStmt ret (AssertStatement l argE) = do
    (argE',cstrsargE) <- tcWithCstrs l "assert" $ tcGuard argE
    checkCstrM l cstrsargE $ CheckAssertion $ fmap typed argE'
    tryAddHypothesis l LocalScope cstrsargE $ HypCondition $ fmap typed argE'
    let t = StmtType $ Set.singleton $ StmtFallthru
    return (AssertStatement (notTyped "tcStmt" l) argE',t)
tcStmt ret (SyscallStatement l n args) = do
    args' <- mapM tcSyscallParam args
    let t = StmtType $ Set.singleton $ StmtFallthru
    isSupportedSyscall l n $ map (typed . loc) args'
    return (SyscallStatement (Typed l t) n args',t)
tcStmt ret (ConstStatement l decl) = do
    decl' <- tcConstDecl LocalScope decl
    let t = StmtType (Set.singleton $ StmtFallthru)
    return (ConstStatement (notTyped "tcStmt" l) decl',t)
tcStmt ret (VarStatement l decl) = do
    decl' <- tcVarDecl LocalScope decl
    let t = StmtType (Set.singleton $ StmtFallthru)
    return (VarStatement (notTyped "tcStmt" l) decl',t)
tcStmt ret (ReturnStatement l Nothing) = do
    tcTopCstrM l $ Unifies (ComplexT Void) ret
    let t = StmtType (Set.singleton StmtReturn)
    return (ReturnStatement (Typed l t) Nothing,t)
tcStmt ret (ReturnStatement l (Just e)) = do
    e' <- tcExpr e
    let et' = typed $ loc e'
    x <- newTypedVar "ret" ret $ Just $ pp e
    tcTopCstrM l $ Coerces (fmap typed e') x
    let t = StmtType (Set.singleton StmtReturn)
    let ex = fmap (Typed l) $ RVariablePExpr ret x
    return (ReturnStatement (Typed l t) (Just ex),t)
tcStmt ret (ContinueStatement l) = do
    let t = StmtType (Set.singleton StmtContinue)
    return (BreakStatement $ Typed l t,t)
tcStmt ret (BreakStatement l) = do
    let t = StmtType (Set.singleton StmtBreak)
    return (BreakStatement $ Typed l t,t)
tcStmt ret (ExpressionStatement l e) = do
    e' <- tcExpr e
    let te = typed $ loc e'
    let t = StmtType (Set.singleton $ StmtFallthru)
    return (ExpressionStatement (Typed l t) e',t)

isSupportedSyscall :: (Monad m,Location loc) => loc -> Identifier -> [Type] -> TcM loc m ()
isSupportedSyscall l n args = return () -- TODO: check specific syscalls?

tcSyscallParam :: (VarsIdTcM loc m,Location loc) => SyscallParameter Identifier loc -> TcM loc m (SyscallParameter VarIdentifier (Typed loc))
tcSyscallParam (SyscallPush l e) = do
    e' <- tcExpr e
    let t = SysT $ SysPush $ typed $ loc e'
    return $ SyscallPush (Typed l t) e'
tcSyscallParam (SyscallReturn l v) = do
    v' <- tcVarName False v
    let t = SysT $ SysRet $ typed $ loc v'
    return $ SyscallReturn (Typed l t) v'
tcSyscallParam (SyscallPushRef l v) = do
    v' <- tcVarName False v
    let t = SysT $ SysRef $ typed $ loc v'
    return $ SyscallPushRef (Typed l t) v'
tcSyscallParam (SyscallPushCRef l e) = do
    e' <- tcExpr e
    let t = SysT $ SysCRef $ typed $ loc e'
    return $ SyscallPushCRef (Typed l t) e'

tcForInitializer :: (VarsIdTcM loc m,Location loc) => ForInitializer Identifier loc -> TcM loc m (ForInitializer VarIdentifier (Typed loc))
tcForInitializer (InitializerExpression Nothing) = return $ InitializerExpression Nothing
tcForInitializer (InitializerExpression (Just e)) = do
    e' <- tcExpr e
    return $ InitializerExpression $ Just e'
tcForInitializer (InitializerVariable vd) = do
    vd' <- tcVarDecl LocalScope vd
    return $ InitializerVariable vd'

tcVarDecl :: (VarsIdTcM loc m,Location loc) => Scope -> VariableDeclaration Identifier loc -> TcM loc m (VariableDeclaration VarIdentifier (Typed loc))
tcVarDecl scope (VariableDeclaration l tyspec vars) = do
    tyspec' <- tcTypeSpec tyspec False
    let ty = typed $ loc tyspec'
    vars' <- mapM (tcVarInit scope ty) vars
    return $ VariableDeclaration (notTyped "tcVarDecl" l) tyspec' vars'

tcVarInit :: (VarsIdTcM loc m,Location loc) => Scope -> Type -> VariableInitialization Identifier loc -> TcM loc m (VariableInitialization VarIdentifier (Typed loc))
tcVarInit scope ty (VariableInitialization l v@(VarName vl vn) szs e) = do
    (ty',szs') <- tcTypeSizes l ty szs
    e' <- mapM (tcExprTy ty') e
    -- add the array size to the type
    let v' = VarName (Typed vl ty') $ mkVarId vn
    -- add variable to the environment
    newVariable scope v' Nothing False -- don't add values to the environment
    return $ VariableInitialization (notTyped "tcVarInit" l) v' szs' e'

tcConstDecl :: (VarsIdTcM loc m,Location loc) => Scope -> ConstDeclaration Identifier loc -> TcM loc m (ConstDeclaration VarIdentifier (Typed loc))
tcConstDecl scope (ConstDeclaration l tyspec vars) = do
    tyspec' <- tcTypeSpec tyspec False
    let ty = typed $ loc tyspec'
    vars' <- mapM (tcConstInit scope ty) vars
    return $ ConstDeclaration (notTyped "tcVarDecl" l) tyspec' vars'

tcConstInit :: (VarsIdTcM loc m,Location loc) => Scope -> Type -> ConstInitialization Identifier loc -> TcM loc m (ConstInitialization VarIdentifier (Typed loc))
tcConstInit scope ty (ConstInitialization l v@(VarName vl vn) szs e) = do
    (ty',szs') <- tcTypeSizes l ty szs
    e' <- mapM (tcExprTy ty') e
    -- add the array size to the type
    vn' <- addConst scope vn
    -- we issue new uniq variables for consts, since they are used in typechecking
    let v' = VarName (Typed vl ty') vn'
    -- add variable to the environment
    newVariable scope v' e' True -- add values to the environment
    return $ ConstInitialization (notTyped "tcVarInit" l) v' szs' e'

    




