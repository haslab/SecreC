{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Statement where

import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Monad
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
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Environment

import Data.Bifunctor
import Data.Traversable
import qualified Data.Foldable as Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Int
import Data.Word

import Safe

import Text.PrettyPrint hiding (equals)

import Control.Monad hiding (mapM)
import Control.Monad.IO.Class
import Control.Monad.State as State
import Control.Monad.Reader as Reader

import Prelude hiding (mapM)

-- | Left-biased merge of two @StmtClass@es
extendStmtClasses :: Set StmtClass -> Set StmtClass -> Set StmtClass
extendStmtClasses s1 s2 = (Set.filter (not . isStmtFallthru) s1) `Set.union` s2

tcStmtsRet :: ProverK loc m => Type -> [Statement Identifier loc] -> TcM m [Statement VarIdentifier (Typed loc)]
tcStmtsRet ret ss = do
    (ss',StmtType st) <- tcStmts ret ss
    isReturnStmt (maybe noloc loc $ headMay ss) st ret 
    return ss'

isReturnStmt :: (ProverK loc m) => loc -> Set StmtClass -> Type -> TcM m ()
isReturnStmt l cs ret = addErrorM l (\err -> TypecheckerError (locpos l) $ NoReturnStatement (pp ret)) $ aux $ Set.toList cs
  where
    aux [StmtFallthru] = equals l ret (ComplexT Void) 
    aux [StmtReturn] = return ()
    aux x = genTcError (locpos l) $ text "Unexpected return class"

tcStmts :: (ProverK loc m) => Type -> [Statement Identifier loc] -> TcM m ([Statement VarIdentifier (Typed loc)],Type)
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
    ssFvs <- liftM Map.keysSet $ fvs $ map (bimap mkVarId id) ss
    (ss',StmtType cs) <- tcStmts ret ss
    -- issue warning for unused variable declarations
    forSetM_ (sBvs `Set.difference` ssFvs) $ \(v::VarIdentifier) -> tcWarn (locpos $ loc s) $ UnusedVariable (pp v)
    return (s':ss',StmtType $ extendStmtClasses c cs)

-- | Typecheck a non-empty statement
tcNonEmptyStmt :: (ProverK loc m) => Type -> Statement Identifier loc -> TcM m (Statement VarIdentifier (Typed loc),Type)
tcNonEmptyStmt ret s = do
    r@(s',StmtType cs) <- tcAddDeps (loc s) "nonempty stmt" $ tcStmt ret s
    when (Set.null cs) $ tcWarn (locpos $ loc s) $ EmptyBranch (pp s)
    return r

-- | Typecheck a statement in the body of a loop
tcLoopBodyStmt :: (ProverK loc m) => Type -> loc -> Statement Identifier loc -> TcM m (Statement VarIdentifier (Typed loc),Type)
tcLoopBodyStmt ret l s = do
    (s',StmtType cs) <- tcAddDeps l "loop" $ tcStmt ret s
    -- check that the body can perform more than iteration
    when (Set.null $ Set.filter isIterationStmtClass cs) $ tcWarn (locpos l) $ SingleIterationLoop (pp s)
    -- return the @StmtClass@ for the whole loop
    let t' = StmtType $ Set.insert (StmtFallthru) (Set.filter (not . isLoopStmtClass) cs)
    return (s',t')
    
-- | Typechecks a @Statement@
tcStmt :: (ProverK loc m) => Type -- ^ return type
    -> Statement Identifier loc -- ^ input statement
    -> TcM m (Statement VarIdentifier (Typed loc),Type)
tcStmt ret (CompoundStatement l s) = do
    (ss',t) <- tcLocal l "tcStmt compound" $ tcStmts ret s
    return (CompoundStatement (Typed l t) ss',t)
tcStmt ret (IfStatement l condE thenS Nothing) = do
    condE' <- tcGuard condE
    (thenS',StmtType cs) <- tcLocal l "tcStmt if then" $ tcNonEmptyStmt ret thenS
    -- an if statement falls through if the condition is not satisfied
    let t = StmtType $ Set.insert (StmtFallthru) cs
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' Nothing,t)
tcStmt ret (IfStatement l condE thenS (Just elseS)) = do
    condE' <- tcGuard condE
    (thenS',StmtType cs1) <- tcLocal l "tcStmt if then" $ tcNonEmptyStmt ret thenS
    (elseS',StmtType cs2) <- tcLocal l "tcStmt if else" $ tcNonEmptyStmt ret elseS 
    let t = StmtType $ cs1 `Set.union` cs2
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' (Just elseS'),t)
tcStmt ret (ForStatement l startE whileE incE ann bodyS) = tcLocal l "tcStmt for" $ do
    startE' <- tcForInitializer startE
    whileE' <- mapM (tcGuard) whileE
    incE' <- mapM (tcExpr) incE
    ann' <- mapM tcLoopAnn ann
    (bodyS',t') <- tcLocal l "tcStmt for body" $ tcLoopBodyStmt ret l bodyS
    return (ForStatement (notTyped "tcStmt" l) startE' whileE' incE' ann' bodyS',t')
tcStmt ret (WhileStatement l condE ann bodyS) = do
    ann' <- mapM tcLoopAnn ann
    condE' <- tcGuard condE
    (bodyS',t') <- tcLocal l "tcStmt while body" $ tcLoopBodyStmt ret l bodyS
    return (WhileStatement (notTyped "tcStmt" l) condE' ann' bodyS',t')
tcStmt ret (PrintStatement (l::loc) argsE) = do
    argsE' <- mapM (tcVariadicArg tcExpr) argsE
    xs <- forM argsE' $ \argE' -> do
        tx <- newTyVar Nothing
        newTypedVar "print" tx $ Just $ ppVariadicArg pp argE'
    topTcCstrM_ l $ SupportedPrint (map (mapFst (fmap typed)) argsE') xs
    let exs = map (fmap (Typed l) . varExpr) xs
    let t = StmtType $ Set.singleton $ StmtFallthru
    return (PrintStatement (Typed l t) (zip exs $ map snd argsE'),t)
tcStmt ret (DowhileStatement l ann bodyS condE) = tcLocal l "tcStmt dowhile" $ do
    ann' <- mapM tcLoopAnn ann
    (bodyS',t') <- tcLoopBodyStmt ret l bodyS
    condE' <- tcGuard condE
    return (DowhileStatement (notTyped "tcStmt" l) ann' bodyS' condE',t')
tcStmt ret (AssertStatement l argE) = do
    (argE',cstrsargE) <- tcWithCstrs l "assert" $ tcGuard argE
    opts <- askOpts
    when (checkAssertions opts) $ topCheckCstrM_ l cstrsargE $ CheckAssertion $ fmap typed argE'
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
    topTcCstrM_ l $ Unifies (ComplexT Void) ret
    let t = StmtType (Set.singleton $ StmtReturn)
    let ret = ReturnStatement (Typed l t) Nothing
    return (ret,t)
tcStmt ret (ReturnStatement l (Just e)) = do
    e' <- tcExpr e
    let et' = typed $ loc e'
    x <- newTypedVar "ret" ret $ Just $ pp e
    topTcCstrM_ l $ Coerces (fmap typed e') x
    let t = StmtType (Set.singleton $ StmtReturn)
    let ex = fmap (Typed l) $ RVariablePExpr ret x
    let ret = ReturnStatement (Typed l t) (Just ex)
    return (ret,t)
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
tcStmt ret (AnnStatement l ann) = do
    (ann') <- mapM tcStmtAnn ann
    let t = StmtType $ Set.singleton StmtFallthru
    return (AnnStatement (Typed l t) ann',t)

tcLoopAnn :: ProverK loc m => LoopAnnotation Identifier loc -> TcM m (LoopAnnotation VarIdentifier (Typed loc))
tcLoopAnn (DecreasesAnn l e) = insideAnnotation $ do
    (e') <- tcGuard e
    return (DecreasesAnn (Typed l $ typed $ loc e') e')
tcLoopAnn (InvariantAnn l e) = insideAnnotation $ do
    (e') <- tcGuard e
    return (InvariantAnn (Typed l $ typed $ loc e') e')

tcStmtAnn :: (ProverK loc m) => StatementAnnotation Identifier loc -> TcM m (StatementAnnotation VarIdentifier (Typed loc))
tcStmtAnn (AssumeAnn l e) = insideAnnotation $ do
    (e') <- tcGuard e
    return (AssumeAnn (Typed l $ typed $ loc e') e')
tcStmtAnn (AssertAnn l e) = insideAnnotation $ do
    (e') <- tcGuard e
    return (AssertAnn (Typed l $ typed $ loc e') e')

isSupportedSyscall :: (Monad m,Location loc) => loc -> Identifier -> [Type] -> TcM m ()
isSupportedSyscall l n args = return () -- TODO: check specific syscalls?

tcSyscallParam :: (ProverK loc m) => SyscallParameter Identifier loc -> TcM m (SyscallParameter VarIdentifier (Typed loc))
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

tcForInitializer :: (ProverK loc m) => ForInitializer Identifier loc -> TcM m (ForInitializer VarIdentifier (Typed loc))
tcForInitializer (InitializerExpression Nothing) = return $ InitializerExpression Nothing
tcForInitializer (InitializerExpression (Just e)) = do
    e' <- tcExpr e
    return $ InitializerExpression $ Just e'
tcForInitializer (InitializerVariable vd) = do
    vd' <- tcVarDecl LocalScope vd
    return $ InitializerVariable vd'

tcVarDecl :: (ProverK loc m) => Scope -> VariableDeclaration Identifier loc -> TcM m (VariableDeclaration VarIdentifier (Typed loc))
tcVarDecl scope (VariableDeclaration l tyspec vars) = do
    (tyspec') <- tcTypeSpec tyspec False
    let ty = typed $ loc tyspec'
    (vars') <- mapM (tcVarInit scope ty) vars
    return (VariableDeclaration (notTyped "tcVarDecl" l) tyspec' vars')

tcVarInit :: (ProverK loc m) => Scope -> Type -> VariableInitialization Identifier loc -> TcM m (VariableInitialization VarIdentifier (Typed loc))
tcVarInit scope ty (VariableInitialization l v@(VarName vl vn) szs e) = do
    (ty',szs') <- tcTypeSizes l ty szs
    e' <- mapM (tcExprTy ty) e
    -- add the array size to the type
    -- do not store the size, since it can change dynamically
    let v' = VarName (Typed vl ty) $ mkVarId vn
    -- add variable to the environment
    newVariable scope v' Nothing False -- don't add values to the environment
    return (VariableInitialization (notTyped "tcVarInit" l) v' szs' e')

tcConstDecl :: (ProverK loc m) => Scope -> ConstDeclaration Identifier loc -> TcM m (ConstDeclaration VarIdentifier (Typed loc))
tcConstDecl scope (ConstDeclaration l tyspec vars) = do
    (tyspec') <- tcTypeSpec tyspec False
    let ty = typed $ loc tyspec'
    (vars') <- mapM (tcConstInit scope ty) vars
    return (ConstDeclaration (notTyped "tcVarDecl" l) tyspec' vars')

tcConstInit :: (ProverK loc m) => Scope -> Type -> ConstInitialization Identifier loc -> TcM m (ConstInitialization VarIdentifier (Typed loc))
tcConstInit scope ty (ConstInitialization l v@(VarName vl vn) szs e) = do
    (ty',szs') <- tcTypeSizes l ty szs
    (e') <- mapM (tcExprTy ty') e
    -- add the array size to the type
    vn' <- addConst scope vn
    -- we issue new uniq variables for consts, since they are used in typechecking
    let v' = VarName (Typed vl ty') vn'
    -- add variable to the environment
    newVariable scope v' e' True -- add values to the environment
    return (ConstInitialization (notTyped "tcVarInit" l) v' szs' e')

    




