{-# LANGUAGE ViewPatterns, ScopedTypeVariables, FlexibleContexts #-}

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
import Data.Maybe

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

tcStmtBlock :: ProverK loc m => loc -> String -> TcM m a -> TcM m a
tcStmtBlock l msg m = tcProgress l $ do
    doResolve <- getDoResolve
    debugTc $ liftIO $ putStrLn $ "tcStmtBlock " ++ pprid (locpos l) ++ " " ++ show doResolve
    if doResolve
        then tcNew (locpos l) msg $ do
            x <- m
            solveTop l msg
            return x
        else tcAddDeps l msg m

tcStmtsRet :: ProverK loc m => loc -> Type -> [Statement Identifier loc] -> TcM m [Statement GIdentifier (Typed loc)]
tcStmtsRet l ret ss = do
    (ss',StmtType st) <- tcStmts ret ss
    isReturnStmt l st ret 
    return ss'

isReturnStmt :: (ProverK loc m) => loc -> Set StmtClass -> Type -> TcM m ()
isReturnStmt l cs ret = do
    ppret <- pp ret
    ppcs <- pp cs
    addErrorM l (\err -> TypecheckerError (locpos l) $ NoReturnStatement (ppret <+> ppcs) $ Just err) $ mapM_ aux $ Set.toList cs
  where
    aux StmtReturn = return ()
    aux (StmtFallthru t) = do
        pp1 <- pp ret
        pp2 <- pp t
        addErrorM l (TypecheckerError (locpos l) . (EqualityException "expression") (pp1) (pp2) . Just) $
            tcCstrM_ l $ Unifies ret t
    aux x = genTcError (locpos l) False $ text "Unexpected return class"

tcStmts :: (ProverK loc m) => Type -> [Statement Identifier loc] -> TcM m ([Statement GIdentifier (Typed loc)],Type)
tcStmts ret [] = return ([],StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void)
tcStmts ret [s] = do
    (s',StmtType c) <- tcStmtBlock (loc s) "stmt" $ tcStmt ret s
    return ([s'],StmtType c)
tcStmts ret (s:ss) = do
    (s',StmtType c) <- tcStmtBlock (loc s) "stmts" $ tcStmt ret s
    -- if the following statements are never executed, issue an error
    case ss of
        [] -> return ()
        ss -> unless (hasStmtFallthru c) $ do
            ppss <- mapM pp ss
            tcError (locpos $ loc (head ss)) $ UnreachableDeadCode (vcat ppss)
    (ss',StmtType cs) <- tcStmts ret ss
    sBvs <- liftM (Map.keysSet . Map.filter (\b -> not b)) $ bvs $ bimap mkVarId (const ()) s
    ssFvs <- fvsSet $ map (bimap mkVarId (const ())) ss
    -- issue warning for unused variable declarations
    forSetM_ (sBvs `Set.difference` ssFvs) $ \(v::VarIdentifier) -> do
        ppv <- pp v
        tcWarn (locpos $ loc s) $ UnusedVariable (ppv)
    return (s':ss',StmtType $ extendStmtClasses c cs)

-- | Typecheck a non-empty statement
tcNonEmptyStmt :: (ProverK loc m) => Type -> Statement Identifier loc -> TcM m (Statement GIdentifier (Typed loc),Type)
tcNonEmptyStmt ret s = do
    r@(s',StmtType cs) <- tcStmtBlock (loc s) "nonempty stmt" $ tcStmt ret s
    when (Set.null cs) $ do
        pps <- pp s
        tcWarn (locpos $ loc s) $ EmptyBranch (pps)
    return r

-- | Typecheck a statement in the body of a loop
tcLoopBodyStmt :: (ProverK loc m) => Type -> loc -> Statement Identifier loc -> TcM m (Statement GIdentifier (Typed loc),Type)
tcLoopBodyStmt ret l s = do
    (s',StmtType cs) <- tcStmtBlock l "loop" $ tcStmt ret s
    -- check that the body can perform more than iteration
    when (Set.null $ Set.filter isIterationStmtClass cs) $ do
        pps <- pp s
        tcWarn (locpos l) $ SingleIterationLoop (pps)
    -- return the @StmtClass@ for the whole loop
    let t' = StmtType $ Set.insert (StmtFallthru $ ComplexT Void) (Set.filter (not . isLoopStmtClass) cs)
    return (s',t')
    
-- | Typechecks a @Statement@
tcStmt :: (ProverK loc m) => Type -- ^ return type
    -> Statement Identifier loc -- ^ input statement
    -> TcM m (Statement GIdentifier (Typed loc),Type)
tcStmt ret (CompoundStatement l s) = do
    (ss',t) <- tcLocal l "tcStmt compound" $ tcStmts ret s
    return (CompoundStatement (Typed l t) ss',t)
tcStmt ret (IfStatement l condE thenS Nothing) = do
    condE' <- tcStmtBlock l "ifguard" $ tcGuard condE
    (thenS',StmtType cs) <- tcLocal l "tcStmt if then" $ tcNonEmptyStmt ret thenS
    -- an if statement falls through if the condition is not satisfied
    let t = StmtType $ Set.insert (StmtFallthru $ ComplexT Void) cs
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' Nothing,t)
tcStmt ret (IfStatement l condE thenS (Just elseS)) = do
    condE' <- tcStmtBlock l "ifguard" $ tcGuard condE
    (thenS',StmtType cs1) <- tcLocal l "tcStmt if then" $ tcNonEmptyStmt ret thenS
    (elseS',StmtType cs2) <- tcLocal l "tcStmt if else" $ tcNonEmptyStmt ret elseS 
    let t = StmtType $ cs1 `Set.union` cs2
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' (Just elseS'),t)
tcStmt ret (ForStatement l startE whileE incE ann bodyS) = tcLocal l "tcStmt for" $ do
    ((startE',whileE',incE',ann',bodyS',t'),rs,ws) <- withDecClassVars $ do
        startE' <- tcStmtBlock l "forinit" $ tcForInitializer startE
        whileE' <- tcStmtBlock l "forguard" $ mapM (tcGuard) whileE
        incE' <- withExprC ReadWriteExpr $ tcStmtBlock l "forinc" $ mapM (tcExpr Nothing) incE
        ann' <- mapM tcLoopAnn ann
        (bodyS',t') <- tcLocal l "tcStmt for body" $ tcLoopBodyStmt ret l bodyS
        return (startE',whileE',incE',ann',bodyS',t')
    debugTc $ do
        ppl <- ppr l
        pprs <- pp rs
        ppws <- pp ws
        locals <- State.gets (Map.keys . localVars)
        pplocals <- pp locals
        liftIO $ putStrLn $ "whileT " ++ ppl ++ ": " ++ show pprs ++ "  :  " ++ show ppws ++ "\n" ++ show pplocals
    return (ForStatement (Typed l $ WhileT rs ws) startE' whileE' incE' ann' bodyS',t')
tcStmt ret (WhileStatement l condE ann bodyS) = do
    ((ann',condE',bodyS',t'),rs,ws) <- withDecClassVars $ do
        ann' <- mapM tcLoopAnn ann
        condE' <- tcStmtBlock l "whileguard" $ tcGuard condE
        (bodyS',t') <- tcLocal l "tcStmt while body" $ tcLoopBodyStmt ret l bodyS
        return (ann',condE',bodyS',t')
    debugTc $ do
        ppl <- ppr l
        pprs <- pp rs
        ppws <- pp ws
        liftIO $ putStrLn $ "whileT " ++ ppl ++ ": " ++ show pprs ++ "  :  " ++ show ppws
    return (WhileStatement (Typed l $ WhileT rs ws) condE' ann' bodyS',t')
tcStmt ret (PrintStatement (l::loc) argsE) = do
    argsE' <- withExprC ReadOnlyExpr $ mapM (tcVariadicArg (tcExpr Nothing)) argsE
    xs <- forM argsE' $ \argE' -> do
        tx <- newTyVar True False Nothing
        pparg <- ppVariadicArg pp argE'
        newTypedVar "print" tx False $ Just pparg
    topTcCstrM_ l $ SupportedPrint (map (\(x,y) -> (False,Left $ fmap typed x,y)) argsE') xs
    let exs = map (fmap (Typed l) . varExpr) xs
    let t = StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void
    return (PrintStatement (Typed l t) (zip exs $ map snd argsE'),t)
tcStmt ret (DowhileStatement l ann bodyS condE) = tcLocal l "tcStmt dowhile" $ do
    ((ann',bodyS',t',condE'),rs,ws) <- withDecClassVars $ do
        ann' <- mapM tcLoopAnn ann
        (bodyS',t') <- tcLoopBodyStmt ret l bodyS
        condE' <- tcGuard condE
        return (ann',bodyS',t',condE')
    debugTc $ do
        ppl <- ppr l
        pprs <- pp rs
        ppws <- pp ws
        liftIO $ putStrLn $ "whileT " ++ ppl ++ ": " ++ show pprs ++ "  :  " ++ show ppws
    return (DowhileStatement (Typed l $ WhileT rs ws) ann' bodyS' condE',t')
tcStmt ret (AssertStatement l argE) = do
    (argE',cstrsargE) <- tcWithCstrs l "assert" $ tcGuard argE
    opts <- askOpts
    when (checkAssertions opts) $ topCheckCstrM_ l cstrsargE $ CheckAssertion $ fmap typed argE'
    tryAddHypothesis l "tcStmt assert" LocalScope checkAssertions cstrsargE $ HypCondition $ fmap typed argE'
    let t = StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void
    return (AssertStatement (notTyped "tcStmt" l) argE',t)
tcStmt ret (SyscallStatement l n args) = do
    args' <- mapM tcSyscallParam args
    let t = StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void
    isSupportedSyscall l n $ map (typed . loc) args'
    return (SyscallStatement (Typed l t) n args',t)
tcStmt ret (VarStatement l decl) = do
    decl' <- tcVarDecl LocalScope decl
    let t = StmtType (Set.singleton $ StmtFallthru $ ComplexT Void)
    return (VarStatement (notTyped "tcStmt" l) decl',t)
tcStmt ret (ReturnStatement l Nothing) = do
    topTcCstrM_ l $ Unifies (ComplexT Void) ret
    let t = StmtType (Set.singleton $ StmtReturn)
    let ret = ReturnStatement (Typed l t) Nothing
    return (ret,t)
tcStmt ret (ReturnStatement l (Just e)) = do
    e' <- withExprC ReadWriteExpr $ tcExpr Nothing e
    let et' = typed $ loc e'
    ppe <- pp e
    x <- tcCoerces l True Nothing (fmap typed e') ret
    let t = StmtType (Set.singleton $ StmtReturn)
    let ex = fmap (Typed l) x
    let ret = ReturnStatement (Typed l t) (Just ex)
    return (ret,t)
tcStmt ret (ContinueStatement l) = do
    let t = StmtType (Set.singleton StmtContinue)
    return (BreakStatement $ Typed l t,t)
tcStmt ret (BreakStatement l) = do
    let t = StmtType (Set.singleton StmtBreak)
    return (BreakStatement $ Typed l t,t)    
tcStmt ret (ExpressionStatement l e) = do
    e' <- withExprC ReadWriteExpr $ tcExpr Nothing e
    let te = typed $ loc e'
    --case e of
    --    BinaryAssign {} -> return ()
    --    otherwise -> topTcCstrM_ l $ Unifies te (ComplexT Void)
    let t = StmtType (Set.singleton $ StmtFallthru te)
    return (ExpressionStatement (Typed l t) e',t)
tcStmt ret (AnnStatement l ann) = do
    (ann') <- mapM tcStmtAnn ann
    let t = StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void
    return (AnnStatement (Typed l t) ann',t)

tcLoopAnn :: ProverK loc m => LoopAnnotation Identifier loc -> TcM m (LoopAnnotation GIdentifier (Typed loc))
tcLoopAnn (DecreasesAnn l isFree e) = tcStmtBlock l "loopann" $ insideAnnotation $ withLeak False $ do
    (e') <- tcAnnExpr Nothing e
    return $ DecreasesAnn (Typed l $ typed $ loc e') isFree e'
tcLoopAnn (InvariantAnn l isFree isLeak e) = tcStmtBlock l "loopann" $ insideAnnotation $ do
    (isLeak',e') <- checkLeak l isLeak $ tcAnnGuard e
    return $ InvariantAnn (Typed l $ typed $ loc e') isFree isLeak' e'

tcStmtAnn :: (ProverK loc m) => StatementAnnotation Identifier loc -> TcM m (StatementAnnotation GIdentifier (Typed loc))
tcStmtAnn (AssumeAnn l isLeak e) = tcStmtBlock l "stmtann" $ insideAnnotation $ do
    (isLeak',e') <- checkLeak l isLeak $ tcAnnGuard e
    return $ AssumeAnn (Typed l $ typed $ loc e') isLeak e'
tcStmtAnn (AssertAnn l isLeak e) = tcStmtBlock l "stmtann" $ insideAnnotation $ do
    (isLeak',e') <- checkLeak l isLeak $ tcAnnGuard e
    return $ AssertAnn (Typed l $ typed $ loc e') isLeak' e'
tcStmtAnn (EmbedAnn l isLeak e) = tcStmtBlock l "stmtann" $ insideAnnotation $ withKind LKind $ do
    (isLeak',(e',t)) <- checkLeak l isLeak $ tcStmt (ComplexT Void) e
    return $ EmbedAnn (Typed l t) isLeak' e'

isSupportedSyscall :: (Monad m,Location loc) => loc -> Identifier -> [Type] -> TcM m ()
isSupportedSyscall l n args = return () -- TODO: check specific syscalls?

tcSyscallParam :: (ProverK loc m) => SyscallParameter Identifier loc -> TcM m (SyscallParameter GIdentifier (Typed loc))
tcSyscallParam (SyscallPush l e) = do
    e' <- withExprC ReadWriteExpr $ tcVariadicArg (tcExpr Nothing) e
    let t = SysT $ SysPush $ typed $ loc $ fst e'
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
    e' <- withExprC ReadWriteExpr $ tcExpr Nothing e
    let t = SysT $ SysCRef $ typed $ loc e'
    return $ SyscallPushCRef (Typed l t) e'

tcForInitializer :: (ProverK loc m) => ForInitializer Identifier loc -> TcM m (ForInitializer GIdentifier (Typed loc))
tcForInitializer (InitializerExpression Nothing) = return $ InitializerExpression Nothing
tcForInitializer (InitializerExpression (Just e)) = do
    e' <- withExprC ReadWriteExpr $ tcExpr Nothing e
    return $ InitializerExpression $ Just e'
tcForInitializer (InitializerVariable vd) = do
    vd' <- tcVarDecl LocalScope vd
    return $ InitializerVariable vd'

tcVarDecl :: (ProverK loc m) => Scope -> VariableDeclaration Identifier loc -> TcM m (VariableDeclaration GIdentifier (Typed loc))
tcVarDecl scope (VariableDeclaration l isConst isHavoc tyspec vars) = do
    (tyspec') <- tcTypeSpec tyspec False False
    let ty = typed $ loc tyspec'
    (vars') <- mapM (tcVarInit isConst isHavoc scope ty) vars
    return (VariableDeclaration (notTyped "tcVarDecl" l) isConst True tyspec' vars')

tcVarInit :: (ProverK loc m) => Bool -> Bool -> Scope -> Type -> VariableInitialization Identifier loc -> TcM m (VariableInitialization GIdentifier (Typed loc))
tcVarInit False isHavoc scope ty (VariableInitialization l v@(VarName vl n) szs e) = do
    (ty',szs') <- tcTypeSizes l ty szs
    e' <- withExprC ReadWriteExpr $ tcDefaultInitExpr l isHavoc ty' szs' e
    -- add the array size to the type
    -- do not store the size, since it can change dynamically
    vn <- addConst scope (True,False) False n
    let v' = VarName (Typed vl ty) vn
    -- add variable to the environment
    isAnn <- getAnn
    newVariable scope False isAnn v' Nothing -- don't add values to the environment
    return (VariableInitialization (notTyped "tcVarInit" l) v' szs' e')
tcVarInit True isHavoc scope ty (VariableInitialization l v@(VarName vl n) szs e) = do
    (ty',szs') <- tcTypeSizes l ty szs
    e' <- withExprC PureExpr $ tcDefaultInitExpr l isHavoc ty' szs' e
    -- add the array size to the type
    vn <- addConst scope (True,True) False n
    let v' = VarName (Typed vl ty') vn
    -- add variable to the environment
    isAnn <- getAnn
    newVariable scope True isAnn v' e'
    return (VariableInitialization (notTyped "tcVarInit" l) v' szs' e')

tcDefaultInitExpr :: ProverK loc m => loc -> IsHavoc -> Type -> Maybe (Sizes GIdentifier (Typed loc)) -> Maybe (Expression Identifier loc) -> TcM m (Maybe (Expression GIdentifier (Typed loc)))
tcDefaultInitExpr l isHavoc ty szs (Just e) = withDef False $ do
    liftM Just $ tcExprTy ty e
tcDefaultInitExpr l True ty szs Nothing = return Nothing
tcDefaultInitExpr l False ty szs Nothing = liftM Just $ withDef True $ do
    x <- liftM varExpr $ newTypedVar "def" ty False Nothing
    let szsl = case szs of
                Nothing -> Nothing
                Just (Sizes xs) -> Just $ map (mapFst $ fmap typed) $ Foldable.toList xs
    topTcCstrM_ l $ Default szsl x
    return $ fmap (Typed l) x

    




