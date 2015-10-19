

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

import Data.Traversable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Control.Monad hiding (mapM)
import Prelude hiding (mapM)

-- | Left-biased merge of two @StmtClass@es
extendStmtClasses :: Set StmtClass -> Set StmtClass -> Set StmtClass
extendStmtClasses s1 s2 = (Set.delete StmtFallthru s1) `Set.union` s2

tcStmts :: Location loc => Type -> [Statement loc] -> TcM loc ([Statement (Typed loc)],Type)
tcStmts ret [] = return ([],StmtType $ Set.singleton StmtFallthru)
tcStmts ret [s] = do
    (s',t) <- tcStmt ret s
    return ([s'],t)
tcStmts ret (s:ss) = do
    (s',StmtType c) <- tcStmt ret s
    -- if the following statements are never executed, issue an error
    when (not (null ss) && Set.member StmtFallthru c) $ tcError (locpos $ loc $ head ss) $ UnreachableDeadCode $ map (fmap locpos) ss
    -- issue warning for unused variable declarations
    forSetM_ (bvs s `Set.difference` fvsFoldable ss) $ \(ScVar l v) -> tcWarn (locpos l) $ UnusedVariable v
    (ss',StmtType cs) <- tcStmts ret ss
    return (s':ss',StmtType $ extendStmtClasses c cs)

-- | Typecheck a non-empty statement
tcNonEmptyStmt :: Location loc => Type -> Statement loc -> TcM loc (Statement (Typed loc),Type)
tcNonEmptyStmt ret s = do
    r@(s',StmtType cs) <- tcStmt ret s
    when (Set.null cs) $ tcWarn (locpos $ loc s) $ EmptyBranch (fmap locpos s)
    return r

-- | Typecheck a statement in the body of a loop
tcLoopBodyStmt :: Location loc => Type -> loc -> Statement loc -> TcM loc (Statement (Typed loc),Type)
tcLoopBodyStmt ret l s = do
    (s',StmtType cs) <- tcStmt ret s
    -- check that the body can perform more than iteration
    when (Set.null $ Set.filter isIterationStmtClass cs) $ tcWarn (locpos l) $ SingleIterationLoop $ fmap locpos s
    -- return the @StmtClass@ for the whole loop
    let t' = StmtType $ Set.insert StmtFallthru (Set.filter (not . isLoopStmtClass) cs)
    return (s',t')
    
-- | Typechecks a @Statement@
tcStmt :: Location loc => Type -- ^ return type
    -> Statement loc -- ^ input statement
    -> TcM loc (Statement (Typed loc),Type)
tcStmt ret (CompoundStatement l s) = do
    (ss',t) <- tcBlock $ tcStmts ret s
    return (CompoundStatement (Typed l t) ss',t)
tcStmt ret (IfStatement l condE thenS Nothing) = do
    condE' <- tcReaderM $ tcGuard condE
    (thenS',StmtType cs) <- tcBlock $ tcNonEmptyStmt ret thenS
    -- an if falls through if the condition is not satisfied
    let t = StmtType $ Set.insert StmtFallthru cs
    return (IfStatement (notTyped l) condE' thenS' Nothing,t)
tcStmt ret (IfStatement l condE thenS (Just elseS)) = do
    condE' <- tcReaderM $ tcGuard condE
    (thenS',StmtType cs1) <- tcBlock $ tcNonEmptyStmt ret thenS
    (elseS',StmtType cs2) <- tcBlock $ tcNonEmptyStmt ret elseS 
    let t = StmtType $ cs1 `Set.union` cs2
    return (IfStatement (notTyped l) condE' thenS' (Just elseS'),t)
tcStmt ret (ForStatement l startE whileE incE bodyS) = tcBlock $ do
    startE' <- tcForInitializer startE
    whileE' <- mapM (tcReaderM . tcGuard) whileE
    incE' <- mapM (liftM fst . tcReaderM . tcExpr) incE
    (bodyS',t') <- tcBlock $ tcLoopBodyStmt ret l bodyS
    return (ForStatement (notTyped l) startE' whileE' incE' bodyS',t')
tcStmt ret (WhileStatement l condE bodyS) = do
    condE' <- tcReaderM $ tcGuard condE
    (bodyS',t') <- tcBlock $ tcLoopBodyStmt ret l bodyS
    return (WhileStatement (notTyped l) condE' bodyS',t')
tcStmt ret (PrintStatement l argsE) = error "tcStmt print statement"
tcStmt ret (DowhileStatement l bodyS condE) = do
    condE' <- tcReaderM $ tcGuard condE
    (bodyS',t') <- tcBlock $ tcLoopBodyStmt ret l bodyS
    return (DowhileStatement (notTyped l) bodyS' condE',t')
tcStmt ret (AssertStatement l argE) = do
    argE' <- tcReaderM $ tcGuard argE
    let t = StmtType $ Set.singleton StmtFallthru
    return (AssertStatement (notTyped l) argE',t)
tcStmt ret (SyscallStatement l sysproc args) = error "tcStmt syscall statement"
tcStmt ret (VarStatement l decl) = do
    decl' <- tcVarDecl LocalScope decl
    let t = StmtType (Set.singleton StmtFallthru)
    return (VarStatement (notTyped l) decl',t)
tcStmt ret (ReturnStatement l Nothing) = do
    tcReaderM $ coerces l Void ret
    let t = StmtType (Set.singleton StmtReturn)
    return (ReturnStatement (Typed l t) Nothing,t)
tcStmt ret (ReturnStatement l (Just e)) = do
    (e',et') <- tcReaderM $ tcExpr e
    tcReaderM $ coerces l et' ret
    let t = StmtType (Set.singleton StmtReturn)
    return (ReturnStatement (Typed l t) (Just e'),t)
tcStmt ret (ContinueStatement l) = do
    let t = StmtType (Set.singleton StmtContinue)
    return (BreakStatement $ Typed l t,t)
tcStmt ret (BreakStatement l) = do
    let t = StmtType (Set.singleton StmtBreak)
    return (BreakStatement $ Typed l t,t)
tcStmt ret (ExpressionStatement l e) = do
    (e',et') <- tcReaderM $ tcExpr e -- we discard the expression's result type
    let t = StmtType (Set.singleton StmtFallthru)
    return (ExpressionStatement (Typed l t) e',t)

tcForInitializer :: Location loc => ForInitializer loc -> TcM loc (ForInitializer (Typed loc))
tcForInitializer (InitializerExpression Nothing) = return $ InitializerExpression Nothing
tcForInitializer (InitializerExpression (Just e)) = do
    (e',t) <- tcReaderM $ tcExpr e
    return $ InitializerExpression $ Just e'
tcForInitializer (InitializerVariable vd) = do
    vd' <- tcVarDecl LocalScope vd
    return $ InitializerVariable vd'

tcVarDecl :: Location loc => Scope -> VariableDeclaration loc -> TcM loc (VariableDeclaration (Typed loc))
tcVarDecl scope (VariableDeclaration l tyspec vars) = do
    tyspec' <- tcTypeSpec tyspec
    let ty = typed $ loc tyspec'
    vars' <- mapM (tcVarInit scope ty) vars
    return $ VariableDeclaration (notTyped l) tyspec' vars'

tcVarInit :: Location loc => Scope -> Type -> VariableInitialization loc -> TcM loc (VariableInitialization (Typed loc))
tcVarInit scope ty (VariableInitialization l v@(VarName vl vn) szs e) = do
    d <- tcReaderM $ typeDim l ty
    szs' <- mapM (tcSizes v d) szs
    e' <- mapM (tcReaderM . tcExprTy (typeBase ty)) e
    -- add the array size to the type
    let v' = VarName (Typed vl (refineTypeSizes ty szs')) vn
    -- add variable to the environment
    newVariable scope v'
    return $ VariableInitialization (notTyped l) v' szs' e'

tcSizes :: Location loc => VarName loc -> Int -> Sizes loc -> TcM loc (Sizes (Typed loc))
tcSizes v d (Sizes szs) = do
    -- check array's dimension
    unless (d == lengthNe szs) $ tcError (locpos $ loc v) $ MismatchingArrayDimension d (lengthNe szs) (fmap locpos v)
    szs' <- mapM (tcDimSizeExpr $ Just v) szs
    return $ Sizes szs'

        




