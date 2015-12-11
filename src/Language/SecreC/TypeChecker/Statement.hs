{-# LANGUAGE FlexibleContexts #-}

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
import Language.SecreC.TypeChecker.Semantics
import Language.SecreC.TypeChecker.Environment

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

import Prelude hiding (mapM)

-- | Left-biased merge of two @StmtClass@es
extendStmtClasses :: Set StmtClass -> Set StmtClass -> Set StmtClass
extendStmtClasses s1 s2 = (Set.filter (not . isStmtFallthru) s1) `Set.union` s2

tcStmts :: (VarsTcM loc,Location loc) => Type -> [Statement Identifier loc] -> TcM loc ([Statement VarIdentifier (Typed loc)],Type)
tcStmts ret [] = return ([],StmtType $ Set.empty)
tcStmts ret [s] = do
    (s,st) <- tcStmt ret s
    return ([s],st)
tcStmts ret (s:ss) = do
    (s',StmtType c) <- tcStmt ret s
    -- if the following statements are never executed, issue an error
    case ss of
        [] -> return ()
        ss -> unless (hasStmtFallthru c) $ tcError (locpos $ loc (head ss)) $ UnreachableDeadCode (vcat $ map pp ss)
    -- issue warning for unused variable declarations
    sBvs <- bvs s
    ssFvs <- fvs ss
    forSetM_ (sBvs `Set.difference` ssFvs) $ \(ScVar v) -> tcWarn (locpos $ loc s) $ UnusedVariable (pp v)
    (ss',StmtType cs) <- tcStmts ret ss
    return (s':ss',StmtType $ extendStmtClasses c cs)

-- | Typecheck a non-empty statement
tcNonEmptyStmt :: (VarsTcM loc,Location loc) => Type -> Statement Identifier loc -> TcM loc (Statement VarIdentifier (Typed loc),Type)
tcNonEmptyStmt ret s = do
    r@(s',StmtType cs) <- tcStmt ret s
    when (Set.null cs) $ tcWarn (locpos $ loc s) $ EmptyBranch (pp s)
    return r

-- | Typecheck a statement in the body of a loop
tcLoopBodyStmt :: (VarsTcM loc,Location loc) => Type -> loc -> Statement Identifier loc -> TcM loc (Statement VarIdentifier (Typed loc),Type)
tcLoopBodyStmt ret l s = do
    (s',StmtType cs) <- tcStmt ret s
    -- check that the body can perform more than iteration
    when (Set.null $ Set.filter isIterationStmtClass cs) $ tcWarn (locpos l) $ SingleIterationLoop (pp s)
    -- return the @StmtClass@ for the whole loop
    let t' = StmtType $ Set.insert (StmtFallthru) (Set.filter (not . isLoopStmtClass) cs)
    return (s',t')
    
-- | Typechecks a @Statement@
tcStmt :: (VarsTcM loc,Location loc) => Type -- ^ return type
    -> Statement Identifier loc -- ^ input statement
    -> TcM loc (Statement VarIdentifier (Typed loc),Type)
tcStmt ret (CompoundStatement l s) = do
    (ss',t) <- tcBlock $ tcStmts ret s
    return (CompoundStatement (Typed l t) ss',t)
tcStmt ret (IfStatement l condE thenS Nothing) = do
    condE' <- tcGuard condE
    (thenS',StmtType cs) <- tcBlock $ tcNonEmptyStmt ret thenS
    -- an if falls through if the condition is not satisfied
    let t = StmtType $ Set.insert (StmtFallthru) cs
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' Nothing,t)
tcStmt ret (IfStatement l condE thenS (Just elseS)) = do
    condE' <- tcGuard condE
    (thenS',StmtType cs1) <- tcBlock $ tcNonEmptyStmt ret thenS
    (elseS',StmtType cs2) <- tcBlock $ tcNonEmptyStmt ret elseS 
    let t = StmtType $ cs1 `Set.union` cs2
    return (IfStatement (notTyped "tcStmt" l) condE' thenS' (Just elseS'),t)
tcStmt ret (ForStatement l startE whileE incE bodyS) = tcBlock $ do
    startE' <- tcForInitializer startE
    whileE' <- mapM tcGuard whileE
    incE' <- mapM (tcExpr) incE
    (bodyS',t') <- tcBlock $ tcLoopBodyStmt ret l bodyS
    return (ForStatement (notTyped "tcStmt" l) startE' whileE' incE' bodyS',t')
tcStmt ret (WhileStatement l condE bodyS) = do
    condE' <- tcGuard condE
    (bodyS',t') <- tcBlock $ tcLoopBodyStmt ret l bodyS
    return (WhileStatement (notTyped "tcStmt" l) condE' bodyS',t')
tcStmt ret (PrintStatement l argsE) = do
    argsE' <- mapM tcExpr argsE
    let targs = map (typed . loc) $ Foldable.toList argsE'
    tcTopCstrM l (SupportedPrint targs)
    let t = StmtType $ Set.singleton $ StmtFallthru
    return (PrintStatement (Typed l t) argsE',t)
tcStmt ret (DowhileStatement l bodyS condE) = tcBlock $ do
    (bodyS',t') <- tcLoopBodyStmt ret l bodyS
    condE' <- tcGuard condE
    return (DowhileStatement (notTyped "tcStmt" l) bodyS' condE',t')
tcStmt ret (AssertStatement l argE) = do
    argE' <- tcGuard argE
    let t = StmtType $ Set.singleton $ StmtFallthru
    return (AssertStatement (notTyped "tcStmt" l) argE',t)
tcStmt ret (SyscallStatement l n args) = do
    args' <- mapM tcSyscallParam args
    let t = StmtType $ Set.singleton $ StmtFallthru
    isSupportedSyscall l n $ map (typed . loc) args'
    return (SyscallStatement (Typed l t) n args',t)
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
    tcTopCstrM l $ Coerces et' ret
    let t = StmtType (Set.singleton StmtReturn)
    return (ReturnStatement (Typed l t) (Just e'),t)
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

isSupportedSyscall :: Location loc => loc -> Identifier -> [Type] -> TcM loc ()
isSupportedSyscall l n args = return () -- TODO: check specific syscalls?

tcSyscallParam :: (VarsTcM loc,Location loc) => SyscallParameter Identifier loc -> TcM loc (SyscallParameter VarIdentifier (Typed loc))
tcSyscallParam (SyscallPush l e) = do
    e' <- tcExpr e
    let t = SysT $ SysPush $ typed $ loc e'
    return $ SyscallPush (Typed l t) e'
tcSyscallParam (SyscallReturn l v) = do
    v' <- tcVarName v
    let t = SysT $ SysRet $ typed $ loc v'
    return $ SyscallReturn (Typed l t) v'
tcSyscallParam (SyscallPushRef l v) = do
    v' <- tcVarName v
    let t = SysT $ SysRef $ typed $ loc v'
    return $ SyscallPushRef (Typed l t) v'
tcSyscallParam (SyscallPushCRef l e) = do
    e' <- tcExpr e
    let t = SysT $ SysCRef $ typed $ loc e'
    return $ SyscallPushCRef (Typed l t) e'

tcForInitializer :: (VarsTcM loc,Location loc) => ForInitializer Identifier loc -> TcM loc (ForInitializer VarIdentifier (Typed loc))
tcForInitializer (InitializerExpression Nothing) = return $ InitializerExpression Nothing
tcForInitializer (InitializerExpression (Just e)) = do
    e' <- tcExpr e
    return $ InitializerExpression $ Just e'
tcForInitializer (InitializerVariable vd) = do
    vd' <- tcVarDecl LocalScope vd
    return $ InitializerVariable vd'

tcVarDecl :: (VarsTcM loc,Location loc) => Scope -> VariableDeclaration Identifier loc -> TcM loc (VariableDeclaration VarIdentifier (Typed loc))
tcVarDecl scope (VariableDeclaration l tyspec vars) = do
    tyspec' <- tcTypeSpec tyspec
    let ty = typed $ loc tyspec'
    cty <- typeToComplexType l ty
    vars' <- mapM (tcVarInit scope cty) vars
    return $ VariableDeclaration (notTyped "tcVarDecl" l) tyspec' vars'

tcVarInit :: (VarsTcM loc,Location loc) => Scope -> ComplexType -> VariableInitialization Identifier loc -> TcM loc (VariableInitialization VarIdentifier (Typed loc))
tcVarInit scope ty (VariableInitialization l v@(VarName vl vn) szs e) = do
    d <- typeDim l ty
    szs' <- mapM (tcSizes ty v d) szs
    let tszs' = fmap (fmap typed) szs'
    ty' <- refineTypeSizes l ty tszs'
    e' <- mapM (tcExprTy $ ComplexT ty') e
    -- add the array size to the type
    let v' = VarName (Typed vl $ ComplexT ty') $ mkVarId vn
    -- add variable to the environment
    let val = maybe NoValue KnownExpression e'
    newVariable scope v' val
    return $ VariableInitialization (notTyped "tcVarInit" l) v' szs' e'

tcSizes :: (VarsTcM loc,Location loc) => ComplexType -> VarName Identifier loc -> Maybe Word64 -> Sizes Identifier loc -> TcM loc (Sizes VarIdentifier (Typed loc))
tcSizes ty v Nothing (Sizes szs) = tcError (locpos $ loc v) $ NoDimensionForMatrixInitialization (varNameId v)
tcSizes ty v (Just d) x@(Sizes szs) = do
    -- check array's dimension
    let ds = toEnum (lengthNe szs)
    unless (d == ds) $ tcError (locpos $ loc v) $ MismatchingArrayDimension (pp ty) d ds $ Right (pp v,pp x)
    szs' <- mapM (\(i,x) -> tcSizeExpr ty i (Just v) x) (fromListNe $ zip [1..] $ Foldable.toList szs)
    return $ Sizes szs'
        




