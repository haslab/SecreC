{-# LANGUAGE TupleSections, ConstraintKinds, ViewPatterns, FlexibleContexts, RankNTypes #-}

module Language.SecreC.Transformation.Simplify where

import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Conversion
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.Prover.Semantics
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Error
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Modules
import Language.SecreC.Prover.Base

import Data.Foldable as Foldable
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Typeable
import Data.Maybe

import Text.PrettyPrint as PP

import Control.Monad.Trans
import Control.Monad hiding (mapAndUnzipM)
import Control.Monad.Except hiding (mapAndUnzipM)
import Control.Monad.Trans.Control
import Control.Monad.Reader (Reader(..),MonadReader(..))
import qualified Control.Monad.Reader as Reader

import System.IO

type SimplifyK loc m = ProverK loc m

type SimplifyM loc m a = SimplifyK loc m => a -> TcM m ([Statement VarIdentifier (Typed loc)],a)
type SimplifyT loc m a = SimplifyM loc m (a VarIdentifier (Typed loc))

type SimplifyG loc m a = SimplifyK loc m => a VarIdentifier (Typed loc) -> TcM m (a VarIdentifier (Typed loc))

simplifyModuleFile :: SimplifyK Position m => Options -> TypedModuleFile -> TcM m TypedModuleFile
simplifyModuleFile opts (Left (t,args,m)) = do
    (args',m') <- simplifyModuleWithPPArgs opts (args,m)
    return $ Left (t,args',m')
simplifyModuleFile opts (Right sci) = return $ Right sci

simplifyModuleWithPPArgs :: SimplifyK loc m => Options -> (PPArgs,Module VarIdentifier (Typed loc)) -> TcM m (PPArgs,Module VarIdentifier (Typed loc))
simplifyModuleWithPPArgs opts (ppargs,x) = liftM (ppargs,) $ simplifyModule opts' x
    where opts' = mappend opts (ppOptions ppargs)

simplifyModule :: Options -> SimplifyG loc m Module
simplifyModule opts m@(Module l n p) = do
    if (simplify opts)
        then do
            when (debugTransformation opts) $
                lift $ liftIO $ hPutStrLn stderr ("Simplifying module " ++ ppr (moduleVarId m) ++ "...")
            p' <- simplifyProgram p
            return $ Module l n p'
        else return m

trySimplify :: SimplifyK Position m => (a -> TcM m a) -> (a -> TcM m a)
trySimplify f x = do
    opts <- askOpts
    if simplify opts
        then f x
        else return x

simplifyInnerDecType :: SimplifyK Position m => InnerDecType -> TcM m InnerDecType
simplifyInnerDecType (ProcType p pid args ret anns body cl) = do
    anns' <- simplifyProcedureAnns anns
    body' <- mapM (simplifyStatements Nothing) body
    return $ ProcType p pid args ret anns' body' cl
simplifyInnerDecType (FunType isLeak p pid args ret anns body cl) = do
    anns' <- simplifyProcedureAnns anns
    mb <- mapM (simplifyExpression True) body
    let (ss,body') = case mb of
                        Nothing -> ([],Nothing)
                        Just (ss,Just body') -> (ss,Just body')
    bodyanns <- stmtsAnns ss
    return $ FunType isLeak p pid args ret (anns' ++ map (procAnn False) bodyanns) body' cl
simplifyInnerDecType (StructType p pid atts cl) = do
    return $ StructType p pid atts cl
simplifyInnerDecType (AxiomType isLeak p pargs anns cl) = do
    anns' <- simplifyProcedureAnns anns
    return $ AxiomType isLeak p pargs anns' cl

simplifyProgram :: SimplifyG loc m Program
simplifyProgram (Program l is gs) = do
    gs' <- mapM simplifyGlobalDeclaration gs
    return $ Program l is gs'

simplifyGlobalDeclaration :: SimplifyG loc m GlobalDeclaration
simplifyGlobalDeclaration (GlobalProcedure l p) = do
    p' <- simplifyProcedureDeclaration p
    return $ GlobalProcedure l p'
simplifyGlobalDeclaration (GlobalFunction l p) = do
    p' <- simplifyFunctionDeclaration p
    return $ GlobalFunction l p'
simplifyGlobalDeclaration (GlobalTemplate l t) = do
    t' <- simplifyTemplateDeclaration t
    return $ GlobalTemplate l t'
simplifyGlobalDeclaration g = return g

--GlobalVariable loc (VariableDeclaration iden loc)
--    | GlobalConst loc (ConstDeclaration iden loc)
--    | GlobalDomain loc (DomainDeclaration iden loc)
--    | GlobalKind loc (KindDeclaration iden loc)
--    | GlobalStructure loc (StructureDeclaration iden loc)

simplifyTemplateDeclaration :: SimplifyG loc m TemplateDeclaration
simplifyTemplateDeclaration (TemplateProcedureDeclaration l args p) = do
    p' <- simplifyProcedureDeclaration p
    return $ TemplateProcedureDeclaration l args p'
simplifyTemplateDeclaration (TemplateFunctionDeclaration l args p) = do
    p' <- simplifyFunctionDeclaration p
    return $ TemplateFunctionDeclaration l args p'
simplifyTemplateDeclaration (TemplateStructureDeclaration l targs s) = do
    s' <- simplifyStructureDeclaration s
    return $ TemplateStructureDeclaration l targs s'
simplifyTemplateDeclaration (TemplateStructureSpecialization l targs tspecs s) = do
    s' <- simplifyStructureDeclaration s
    return $ TemplateStructureSpecialization l targs tspecs s'

simplifyStructureDeclaration :: SimplifyG loc m StructureDeclaration
simplifyStructureDeclaration s = return s

simplifyProcedureDeclaration :: SimplifyG loc m ProcedureDeclaration
simplifyProcedureDeclaration (OperatorDeclaration l ret op args anns body) = do
    anns' <- simplifyProcedureAnns anns
    body' <- simplifyStatements Nothing body
    return $ OperatorDeclaration l ret op args anns' body'
simplifyProcedureDeclaration (ProcedureDeclaration l ret op args anns body) = do
    anns' <- simplifyProcedureAnns anns
    body' <- simplifyStatements Nothing body
    return $ ProcedureDeclaration l ret op args anns' body'

simplifyFunctionDeclaration :: SimplifyG loc m FunctionDeclaration
simplifyFunctionDeclaration (OperatorFunDeclaration l isLeak ret op args anns body) = do
    anns' <- simplifyProcedureAnns anns
    (ss,Just body') <- simplifyExpression True body
    bodyanns <- stmtsAnns ss
    return $ OperatorFunDeclaration l isLeak ret op args (anns' ++ map (procAnn False) bodyanns) body'
simplifyFunctionDeclaration (FunDeclaration l isLeak ret op args anns body) = do
    anns' <- simplifyProcedureAnns anns
    (ss,Just body') <- simplifyExpression True body
    bodyanns <- stmtsAnns ss
    return $ FunDeclaration l isLeak ret op args (anns' ++ map (procAnn False) bodyanns) body'

simplifyVariableDeclaration :: SimplifyK loc m => VariableDeclaration VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyVariableDeclaration (VariableDeclaration l t vs) = do
    (xs,t') <- simplifyTypeSpecifier False t
    xs' <- concatMapM (simplifyVariableInitialization t') $ Foldable.toList vs
    return $ xs ++ xs'  
    
simplifyVariableInitialization :: SimplifyK loc m => TypeSpecifier VarIdentifier (Typed loc) -> VariableInitialization VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyVariableInitialization t (VariableInitialization l v szs mbe) = do
    (ss,szs') <- simplifyMaybeSizes False szs
    let def = VariableDeclaration l t $ WrapNe $ VariableInitialization l v szs' Nothing
    ass <- case mbe of
        Nothing -> return []
        Just e -> do
            (ss',e') <- simplifyExpression False e
            let ass' = maybe [] (\e -> [ExpressionStatement l $ BinaryAssign l (varExpr v) (BinaryAssignEqual noloc) e]) e'
            return (ss'++ass')
    return (ss ++ VarStatement l def:ass)

simplifyConstDeclaration :: SimplifyK loc m => ConstDeclaration VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyConstDeclaration (ConstDeclaration l t vs) = do
    (xs,t') <- simplifyTypeSpecifier False t
    xs' <- concatMapM (simplifyConstInitialization t) $ Foldable.toList vs
    return $ xs ++ xs'  
    
simplifyConstInitialization :: SimplifyK loc m => TypeSpecifier VarIdentifier (Typed loc) -> ConstInitialization VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyConstInitialization t (ConstInitialization l v szs mbe) = do
    (ss,szs') <- simplifyMaybeSizes False szs
    let def = ConstDeclaration l t $ WrapNe $ ConstInitialization l v szs' Nothing
    ass <- case mbe of
        Nothing -> return []
        Just e -> do
            (ss',e') <- simplifyExpression False e
            let ass' = maybe [] (\e -> [ExpressionStatement l $ BinaryAssign l (varExpr v) (BinaryAssignEqual noloc) e]) e'
            return (ss'++ass')
    return (ss ++ ConstStatement l def:ass)

simplifyTypeSpecifier :: Bool -> SimplifyT loc m TypeSpecifier
simplifyTypeSpecifier isExpr (TypeSpecifier l s t d) = do
    (ss,t') <- simplifyDatatypeSpecifier isExpr t
    (ss',d') <- simplifyMaybe (simplifyDimtypeSpecifier isExpr) d
    return (ss++ss',TypeSpecifier l s t' d')

simplifyDimtypeSpecifier :: Bool -> SimplifyT loc m DimtypeSpecifier
simplifyDimtypeSpecifier isExpr (DimSpecifier l e) = do
    (ss,Just e') <- simplifyExpression isExpr e
    return (ss,DimSpecifier l e')

simplifyDatatypeSpecifier :: Bool -> SimplifyT loc m DatatypeSpecifier
simplifyDatatypeSpecifier isExpr t@(PrimitiveSpecifier {}) = return ([],t)
simplifyDatatypeSpecifier isExpr t@(VariableSpecifier {}) = return ([],t)
simplifyDatatypeSpecifier isExpr (TemplateSpecifier l n args) = do
    (ss,args') <- simplifyList (simplifyVariadic (simplifyTemplateTypeArgument isExpr)) args
    return (ss,TemplateSpecifier l n args')
simplifyDatatypeSpecifier isExpr (MultisetSpecifier l b) = do
    (ss,b') <- simplifyDatatypeSpecifier isExpr b
    return (ss,MultisetSpecifier l b')

simplifyTemplateTypeArgument :: Bool -> SimplifyT loc m TemplateTypeArgument
simplifyTemplateTypeArgument isExpr a@(GenericTemplateTypeArgument l arg) = return ([],a)
simplifyTemplateTypeArgument isExpr a@(TemplateTemplateTypeArgument l n args) = return ([],a)
simplifyTemplateTypeArgument isExpr a@(PrimitiveTemplateTypeArgument {}) = return ([],a)
simplifyTemplateTypeArgument isExpr (ExprTemplateTypeArgument l e) = do
    (ss,Just e') <- simplifyExpression isExpr e
    return (ss,ExprTemplateTypeArgument l e')
simplifyTemplateTypeArgument isExpr a@(PublicTemplateTypeArgument {}) = return ([],a)

simplifyMaybeSizes :: Bool -> SimplifyM loc m (Maybe (Sizes VarIdentifier (Typed loc)))
simplifyMaybeSizes isExpr Nothing = return ([],Nothing)
simplifyMaybeSizes isExpr (Just (Sizes es)) = do
    (ss,es') <- simplifyVariadicExpressions isExpr $ Foldable.toList es
    if null es'
        then return (ss,Nothing)
        else return (ss,Just $ Sizes $ fromListNe es')

-- the splitted statements and expression must be pure
simplifyExpression :: SimplifyK loc m => Bool -> Expression VarIdentifier (Typed loc) -> TcM m ([Statement VarIdentifier (Typed loc)],Maybe (Expression VarIdentifier (Typed loc)))
simplifyExpression isExpr (ProcCallExpr l n ts es) = do
    (ss,ts') <- simplifyMaybe (simplifyList (simplifyVariadic (simplifyTemplateTypeArgument isExpr))) ts
    (ss',es') <- simplifyVariadicExpressions isExpr es
    mb <- inlineProcCall isExpr (unTyped l) (Left $ procedureNameId n) (typed $ loc n) es'
    case mb of
        Nothing -> return (ss++ss',Just $ ProcCallExpr l n ts' es')
        Just (ss'',res) -> return (ss++ss'++ss'',res)
simplifyExpression isExpr e@(BinaryExpr l e1 o e2) = do
    (ss1,Just e1') <- simplifyExpression isExpr e1
    (ss2,Just e2') <- simplifyExpression isExpr e2
    mb <- inlineProcCall isExpr (unTyped l) (Right $ fmap typed o) (typed $ loc o) [(e1',False),(e2',False)]
    case mb of
        Nothing -> return (ss1++ss2,Just $ BinaryExpr l e1' o e2')
        Just (ss3,res) -> return (ss1++ss2++ss3,res)
simplifyExpression isExpr (UnaryExpr l o e) = do
    (ss,Just e') <- simplifyExpression isExpr e
    mb <- inlineProcCall isExpr (unTyped l) (Right $ fmap typed o) (typed $ loc o) [(e',False)]
    case mb of
        Nothing -> return (ss,Just $ UnaryExpr l o e')
        Just (ss',res) -> return (ss++ss',res)
simplifyExpression isExpr (CondExpr l c e1 e2) = do
    (ssc,Just c') <- simplifyExpression isExpr c
    (ss1,Just e1') <- simplifyExpression isExpr e1
    (ss2,Just e2') <- simplifyExpression isExpr e2
    return (ssc++ss1++ss2,Just $ CondExpr l c' e1' e2')
simplifyExpression isExpr (BinaryAssign l e1 bop e2) = do
    let mb_op = binAssignOpToOp bop
    (ss,Just e2') <- case mb_op of
        Just op -> simplifyExpression isExpr (BinaryExpr l e1 op e2)
        Nothing -> simplifyExpression isExpr e2
    return (ss,Just $ BinaryAssign l e1 (BinaryAssignEqual l) e2')
simplifyExpression isExpr (PostIndexExpr l e s) = do
    (ss1,Just e') <- simplifyExpression isExpr e
    (ss2,s') <- simplifySubscript isExpr s
    return (ss1++ss2,Just $ PostIndexExpr l e' s')
simplifyExpression isExpr (QualExpr l e t) = do
    (sse,Just e') <- simplifyExpression isExpr e
    (sst,t') <- simplifyTypeSpecifier isExpr t
    return (sse++sst,Just $ QualExpr l e' t')
simplifyExpression isExpr e = return ([],Just e)

simplifySubscript :: Bool -> SimplifyT loc m Subscript
simplifySubscript isExpr s = return ([],s)

--simplifyExpression (QualExpr l e t) = do
--    | DomainIdExpr loc (SecTypeSpecifier VarIdentifier loc)
--    | BytesFromStringExpr loc (Expression VarIdentifier loc)
--    | StringFromBytesExpr loc (Expression VarIdentifier loc)
--    | VArraySizeExpr loc (Expression VarIdentifier loc)
--    | SelectionExpr loc (Expression VarIdentifier loc) (AttributeName VarIdentifier loc)

unfoldVariadicExpr :: SimplifyK loc m => (Expression VarIdentifier loc,IsVariadic) -> TcM m [Expression VarIdentifier loc]
unfoldVariadicExpr (e,False) = return [e]
unfoldVariadicExpr (ArrayConstructorPExpr _ es,True) = return es
unfoldVariadicExpr ve = genError (locpos $ loc $ fst ve) $ text "unfoldVariadicExpr"

bindProcArgs :: SimplifyK loc m => Bool -> loc -> [(Bool,Constrained Var,IsVariadic)] -> [Expression VarIdentifier (Typed loc)] -> TcM m ([Statement VarIdentifier (Typed loc)],Map VarIdentifier (Expression VarIdentifier (Typed loc)))
bindProcArgs isExpr l [] [] = return ([],Map.empty)
bindProcArgs isExpr l (v:vs) es = do
    (es',ss,substs) <- bindProcArg isExpr l v es
    (ss',substs') <- bindProcArgs isExpr l vs es'
    return (ss++ss',Map.union substs substs')

bindProcArg :: SimplifyK loc m => Bool -> loc -> (Bool,Constrained Var,IsVariadic) -> [Expression VarIdentifier (Typed loc)] -> TcM m ([Expression VarIdentifier (Typed loc)],[Statement VarIdentifier (Typed loc)],Map VarIdentifier (Expression VarIdentifier (Typed loc)))
bindProcArg False l (False,Constrained v _,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier False t
    let tl = notTyped "bind" l
    let def = VarStatement tl $ VariableDeclaration tl t' $ WrapNe $ VariableInitialization tl (fmap (Typed l) v) Nothing $ Just e
    return (es,ss1++[def],Map.empty)
bindProcArg True l (False,Constrained v _,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier True t
    let tl = notTyped "bind" l
    return (es,ss1,Map.singleton (varNameId v) e)
bindProcArg False l (True,Constrained v _,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier False t
    let tl = notTyped "bind" l
    let def = ConstStatement tl $ ConstDeclaration tl t' $ WrapNe $ ConstInitialization tl (fmap (Typed l) v) Nothing $ Just e
    return (es,ss1++[def],Map.empty)
bindProcArg True l (True,Constrained v _,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier True t
    let tl = notTyped "bind" l
    return (es,ss1,Map.singleton (varNameId v) e)
bindProcArg isExpr l (_,Constrained v _,True) es = do
    sz <- evaluateIndexExpr (locpos l) =<< typeSize (locpos l) (loc v)
    let (es1,es2) = splitAt (fromEnum sz) es
    return (es2,[],Map.singleton (varNameId v) $ ArrayConstructorPExpr (Typed l $ loc v) es1)

simplifyProcedureAnns :: SimplifyK loc m => [ProcedureAnnotation VarIdentifier (Typed loc)] -> TcM m [ProcedureAnnotation VarIdentifier (Typed loc)]
simplifyProcedureAnns = liftM concat . mapM simplifyProcedureAnn

simplifyProcedureAnn :: SimplifyK loc m => ProcedureAnnotation VarIdentifier (Typed loc) -> TcM m [ProcedureAnnotation VarIdentifier (Typed loc)]
simplifyProcedureAnn (RequiresAnn l isFree isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- stmtsAnns ss
    return $ map (procAnn False) anns ++ [RequiresAnn l isFree isLeak e']
simplifyProcedureAnn (EnsuresAnn l isFree isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- stmtsAnns ss
    return $ map (procAnn True) anns ++ [EnsuresAnn l isFree isLeak e']

procAnn :: Bool -> StatementAnnotation VarIdentifier (Typed loc) -> ProcedureAnnotation VarIdentifier (Typed loc)
procAnn True (AssertAnn l isLeak e) = EnsuresAnn l False isLeak e
procAnn True (AssumeAnn l isLeak e) = EnsuresAnn l True isLeak e
procAnn False (AssertAnn l isLeak e) = RequiresAnn l False isLeak e
procAnn False (AssumeAnn l isLeak e) = RequiresAnn l True isLeak e

splitProcAnns :: [ProcedureAnnotation iden loc] -> ([StatementAnnotation iden loc],[StatementAnnotation iden loc])
splitProcAnns [] = ([],[])
splitProcAnns (RequiresAnn p isFree isLeak e:xs) = let (l,r) = splitProcAnns xs in (k p isLeak e:l,r)
    where k = if isFree then AssumeAnn else AssertAnn
splitProcAnns (EnsuresAnn p isFree isLeak e:xs) = let (l,r) = splitProcAnns xs in (l,k p isLeak e:r)
    where k = if isFree then AssumeAnn else AssertAnn

simplifyStatementAnns :: SimplifyK loc m => [StatementAnnotation VarIdentifier (Typed loc)] -> TcM m [StatementAnnotation VarIdentifier (Typed loc)]
simplifyStatementAnns = liftM concat . mapM simplifyStatementAnn

simplifyStatementAnn :: SimplifyK loc m => StatementAnnotation VarIdentifier (Typed loc) -> TcM m [StatementAnnotation VarIdentifier (Typed loc)]
simplifyStatementAnn (AssumeAnn l isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- stmtsAnns ss
    return $ anns ++ [AssumeAnn l isLeak e']
simplifyStatementAnn (AssertAnn l isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- stmtsAnns ss
    return $ anns ++ [AssertAnn l isLeak e']

stmtsAnns :: (PP iden,SimplifyK loc m) => [Statement iden loc] -> TcM m [StatementAnnotation iden loc]
stmtsAnns = liftM concat . mapM stmtAnns

stmtAnns :: (PP iden,SimplifyK loc m) => Statement iden loc -> TcM m [StatementAnnotation iden loc]
stmtAnns (AnnStatement _ anns) = return anns
stmtAnns (CompoundStatement _ ss) = stmtsAnns ss
stmtAnns s = genError (locpos $ loc s) $ text "expected an annotation but found statement" <+> pp s

-- inlines a procedures
-- we assume that typechecking has already tied the procedure's type arguments
inlineProcCall :: SimplifyK loc m => Bool -> loc -> PIdentifier -> Type -> [(Expression VarIdentifier (Typed loc),IsVariadic)] -> TcM m (Maybe ([Statement VarIdentifier (Typed loc)],Maybe (Expression VarIdentifier (Typed loc))))
inlineProcCall False l n t@(DecT d@(DecType _ _ _ _ _ _ _ _ (ProcType _ _ args ret ann (Just body) c))) es = do
    liftIO $ putStrLn $ "inlineProcFalse " ++ ppr n ++ " " ++ ppr es ++ " " ++ ppr t
    es' <- concatMapM unfoldVariadicExpr es
    (decls,substs) <- bindProcArgs False l args es'
    ann' <- subst "inlineProcCall" (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) ann
    body' <- subst "inlineProcCall" (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) body
    mb <- type2TypeSpecifier l ret
    case mb of
        Just t -> do
            res <- liftM (VarName (Typed l ret)) $ genVar (mkVarId "res")
            let ssres = Map.singleton (mkVarId "\\result") (varExpr res)
            ann'' <- subst "inlineProcCall" (substsFromMap ssres) False Map.empty ann'
            let (reqs,ens) = splitProcAnns ann''
            (ss1,t') <- simplifyTypeSpecifier False t
            let tl = notTyped "inline" l
            let def = VarStatement tl $ VariableDeclaration tl t' $ WrapNe $ VariableInitialization tl res Nothing Nothing
            reqs' <- simplifyStatementAnns reqs
            ss <- simplifyStatements (Just res) body'
            ens' <- simplifyStatementAnns ens
            return $ Just (decls++ss1++[def,compoundStmt l ([annStmt l reqs']++ss++[annStmt l ens'])],Just $ varExpr res)
        Nothing -> do
            let (reqs,ens) = splitProcAnns ann'
            reqs' <- simplifyStatementAnns reqs
            ss <- simplifyStatements Nothing body'
            ens' <- simplifyStatementAnns ens
            return $ Just ([compoundStmt l (decls++[annStmt l reqs']++ss++[annStmt l ens'])],Nothing)
inlineProcCall False l n t@(DecT d@(DecType _ _ _ _ _ _ _ _ (FunType isLeak _ _ args ret ann (Just body) c))) es = do
    liftIO $ putStrLn $ "inlineFunFalse " ++ ppr n ++ " " ++ ppr es ++ " " ++ ppr t
    es' <- concatMapM unfoldVariadicExpr es
    (decls,substs) <- bindProcArgs False l args es'
    res <- liftM (VarName (Typed l ret)) $ genVar (mkVarId "res")
    let ssres = Map.singleton (mkVarId "\\result") (varExpr res)
    ann' <- subst "inlineProcCall" (substsFromMap $ Map.union substs ssres) False Map.empty $ map (fmap (fmap (updpos l))) ann
    body' <- subst "inlineProcCall" (substsFromMap substs) False Map.empty $ fmap (fmap (updpos l)) body
    t <- type2TypeSpecifierNonVoid l ret
    let (reqs,ens) = splitProcAnns ann'
    (ss1,t') <- simplifyTypeSpecifier False t
    let tl = notTyped "inline" l
    let def = VarStatement tl $ VariableDeclaration tl t' $ WrapNe $ VariableInitialization tl res Nothing Nothing
    reqs' <- simplifyStatementAnns reqs
    (ss,Just body'') <- simplifyExpression False body'
    let sbody = [ExpressionStatement tl $ BinaryAssign (loc res) (varExpr res) (BinaryAssignEqual tl) body'']
    ens' <- simplifyStatementAnns ens
    return $ Just (decls++ss1++[def,compoundStmt l ([annStmt l reqs']++ss++sbody++[annStmt l ens'])],Just $ varExpr res)
inlineProcCall True l n t@(DecT d@(DecType _ _ _ _ _ _ _ _ (FunType isLeak _ _ args ret ann (Just body) c))) es = do
    liftIO $ putStrLn $ "inlineFunTrue " ++ ppr n ++ " " ++ ppr es ++ " " ++ ppr t
    es' <- concatMapM unfoldVariadicExpr es
    (decls,substs) <- bindProcArgs True l args es'
    body' <- subst "inlineProcCall" (substsFromMap substs) False Map.empty $ fmap (fmap (updpos l)) body
    (ss,Just body'') <- simplifyExpression True body'
    let ssret = Map.singleton (mkVarId "\\result") body''
    ann' <- subst "inlineProcCall" (substsFromMap $ Map.union substs ssret) False Map.empty $ map (fmap (fmap (updpos l))) ann
    t <- type2TypeSpecifierNonVoid l ret
    let (reqs,ens) = splitProcAnns ann'
    (ss1,t') <- simplifyTypeSpecifier True t
    let tl = notTyped "inline" l
    reqs' <- simplifyStatementAnns reqs
    ens' <- simplifyStatementAnns ens
    return $ Just (decls++ss1++[compoundStmt l ([annStmt l reqs']++ss++[annStmt l ens'])],Just body'')
inlineProcCall isExpr l n t es = do
    liftIO $ putStrLn $ "not inline " ++ ppr isExpr ++ " " ++ ppr n ++ " " ++ ppr es ++ " " ++ ppr t
    return Nothing

simplifyStmts :: SimplifyK loc m => Maybe (VarName VarIdentifier (Typed loc)) -> [Statement VarIdentifier (Typed loc)] -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyStmts ret ss = do
    opts <- askOpts
    if simplify opts
        then simplifyStatements ret ss
        else return ss

simplifyStatements :: SimplifyK loc m => Maybe (VarName VarIdentifier (Typed loc)) -> [Statement VarIdentifier (Typed loc)] -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyStatements ret [] = return []
simplifyStatements ret (s:ss) = do
    ss1 <- simplifyStatement ret s
    ss2 <- simplifyStatements ret ss
    return (ss1++ss2)

simplifyStatement :: SimplifyK loc m => Maybe (VarName VarIdentifier (Typed loc)) -> Statement VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyStatement ret (CompoundStatement l ss) = do
    ss' <- simplifyStatements ret ss
    return [CompoundStatement l ss']
simplifyStatement ret (IfStatement l c s1 s2) = do
    (ss,Just c') <- simplifyExpression False c
    s1' <- simplifyStatement ret s1
    s2' <- simplifyStatements ret $ maybeToList s2
    return $ (ss++[IfStatement l c' (compoundStmt (unTyped l) s1') (if null s2 then Nothing else Just (compoundStmt (unTyped l) s2'))])
simplifyStatement Nothing (ReturnStatement l Nothing) = return []
simplifyStatement Nothing (ReturnStatement l (Just e)) = return [ReturnStatement l (Just e)]
simplifyStatement ret (ReturnStatement l (Just e)) = do
    (ss,e') <- simplifyExpression False e
    case (ret,e') of
        (Just v,Just e') -> return (ss++[ExpressionStatement l $ BinaryAssign (loc v) (varExpr v) (BinaryAssignEqual l) e'])
        (Nothing,Nothing) -> return ss
        otherwise -> genError (locpos $ unTyped l) $ text "simplifyStatement: mismamtching return type"
simplifyStatement ret (ReturnStatement l e) = genError (locpos $ unTyped l) $ text "simplifyStatement: return statement"
simplifyStatement ret (AssertStatement l e) = do
    (ss,e') <- simplifyExpression False e
    let s' = maybe [] (\e -> [AssertStatement l e]) e'
    return (ss++s')
simplifyStatement ret (ExpressionStatement l e) = do
    (ss,e') <- simplifyExpression False e
    let s' = maybe [] (\e -> [ExpressionStatement l e]) e'
    return (ss++s')
simplifyStatement ret (VarStatement l v) = do
    simplifyVariableDeclaration v
simplifyStatement ret (ConstStatement l v) = do
    simplifyConstDeclaration v
simplifyStatement ret (WhileStatement l c ann s) = do
    let p = unTyped l
    let tl = notTyped "inline" p
    let ty = loc c
    t' <- type2TypeSpecifierNonVoid p $ typed ty
    wcond <- liftM (VarName ty) $ genVar (mkVarId "wcond")
    let def = VarStatement tl $ VariableDeclaration tl t' $ WrapNe $ VariableInitialization tl wcond Nothing Nothing
    let assign = ExpressionStatement l $ BinaryAssign (loc wcond) (varExpr wcond) (BinaryAssignEqual l) c
    let ifbreak = IfStatement tl (negBoolExprLoc $ varExpr wcond) (BreakStatement tl) Nothing
    s' <- simplifyStatement ret $ compoundStmt (unTyped l) $ [assign,ifbreak,s]
    return [def,WhileStatement l (fmap (Typed p) trueExpr) ann $ compoundStmt (unTyped l) s']
simplifyStatement ret (ForStatement l e c i ann s) = do
    ss <- simplifyForInitializer e
    s' <- simplifyStatement ret s
    return (ss++[ForStatement l (InitializerExpression Nothing) c i ann $ compoundStmt (unTyped l) s'])
simplifyStatement ret (DowhileStatement l ann s c) = do
    s' <- simplifyStatement ret s
    (ss,Just c') <- simplifyExpression False c
    return [DowhileStatement l ann (compoundStmt (unTyped l) $ s'++ss) c']
simplifyStatement ret (PrintStatement l es) = do
    (ss,es') <- simplifyVariadicExpressions False es
    return (ss++[PrintStatement l es'])
simplifyStatement ret (AnnStatement l anns) = do
    anns' <- simplifyStatementAnns anns
    return [AnnStatement l anns']
simplifyStatement ret s = return [s]

--    | SyscallStatement loc String [SyscallParameter iden loc]

simplifyForInitializer :: SimplifyK loc m => ForInitializer VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyForInitializer i@(InitializerExpression Nothing) = return []
simplifyForInitializer (InitializerExpression (Just e)) = do
    (ss,e') <- simplifyExpression False e
    let s' = maybe [] (\e -> [ExpressionStatement (loc e) e]) e'
    return (ss++s')
simplifyForInitializer (InitializerVariable vd) = do
    simplifyVariableDeclaration vd

simplifyList :: SimplifyM loc m a -> SimplifyM loc m [a]
simplifyList m xs = do
    (ss,xs') <- mapAndUnzipM m xs
    return (concat ss,xs')

simplifyVariadic :: SimplifyM loc m a -> SimplifyM loc m (a,IsVariadic)
simplifyVariadic m (x,isVariadic) = do
    (ss,x') <- m x
    return (ss,(x',isVariadic))

simplifyVariadicExpressions :: Bool -> SimplifyM loc m [(Expression VarIdentifier (Typed loc),IsVariadic)]
simplifyVariadicExpressions isExpr es = do
    (ss,es') <- mapAndUnzipM (simplifyVariadicExpression isExpr) es
    return (concat ss,concat es')

simplifyVariadicExpression :: SimplifyK loc m => Bool -> (Expression VarIdentifier (Typed loc),IsVariadic) -> TcM m ([Statement VarIdentifier (Typed loc)],[(Expression VarIdentifier (Typed loc),IsVariadic)])
simplifyVariadicExpression isExpr (e,isVariadic) = do
    (ss,Just e') <- simplifyExpression isExpr e
    case (e',isVariadic) of
        (ArrayConstructorPExpr l es,True) -> return (ss,map (,False) es)
        p -> return (ss,[p])
        
simplifyMaybe :: SimplifyM loc m a -> SimplifyM loc m (Maybe a) 
simplifyMaybe m Nothing = return ([],Nothing)
simplifyMaybe m (Just x) = do
    (ss,x') <- m x
    return (ss,Just x')

simplifySizes :: Bool -> SimplifyM loc m (Maybe (Sizes VarIdentifier (Typed loc)))
simplifySizes isExpr = simplifyMaybe $ \(Sizes xs) -> do
    (ss,xs') <- simplifyVariadicExpressions isExpr (Foldable.toList xs)
    return (ss,Sizes $ fromListNe xs')


