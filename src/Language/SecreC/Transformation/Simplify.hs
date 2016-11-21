{-# LANGUAGE TupleSections, ConstraintKinds, ViewPatterns, FlexibleContexts, RankNTypes #-}

module Language.SecreC.Transformation.Simplify where

import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Utils as Utils
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Conversion
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
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
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Typeable
import Data.Maybe
import Data.List as List

import Safe

import Text.PrettyPrint as PP

import Control.Monad.Trans
import Control.Monad hiding (mapAndUnzipM)
import Control.Monad.Except hiding (mapAndUnzipM)
import Control.Monad.Trans.Control
import Control.Monad.Reader (Reader(..),ReaderT(..),MonadReader(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.Identity
import Control.Monad.Trans.Identity

import System.IO

type SimplifyK loc m = ProverK loc m

type SimplifyM m = (TcM m)
type SimplifyCont loc m a = SimplifyK loc m => a -> SimplifyM m ([Statement GIdentifier (Typed loc)],a)
type SimplifyT loc m a = SimplifyCont loc m (a GIdentifier (Typed loc))

type SimplifyG loc m a = SimplifyK loc m => a GIdentifier (Typed loc) -> SimplifyM m (a GIdentifier (Typed loc))

tryRunSimplify :: SimplifyK Position m => (a -> SimplifyM m a) -> (a -> TcM m a)
tryRunSimplify m x = runSimplify $ m x

runSimplify :: SimplifyK Position m => SimplifyM m a -> TcM m a
runSimplify m = m

withCondExpr :: SimplifyK loc m => Expression GIdentifier (Typed loc) -> SimplifyM m ([Statement GIdentifier (Typed loc)],a) -> SimplifyM m ([Statement GIdentifier (Typed loc)],a)
withCondExpr c m = do
    (ss,x) <- m
    ss' <- mapM addStmtCond ss
    return (ss',x)
  where
    addStmtCond (CompoundStatement l s) = do
        s' <- mapM addStmtCond s
        return $ CompoundStatement l s'
    addStmtCond (AnnStatement l s) = do
        s' <- mapM addAnnStmtCond s
        return $ AnnStatement l s'
    addAnnStmtCond (AssumeAnn l isLeak e) = do
        return $ AssumeAnn l isLeak $ impliesExprLoc c e
    addAnnStmtCond (AssertAnn l isLeak e) = do
        return $ AssertAnn l isLeak $ impliesExprLoc c e
    addAnnStmtCond (EmbedAnn l isLeak s) = do
        s' <- addStmtCond s
        return $ EmbedAnn l isLeak s'

simplifyModuleFile :: SimplifyK Position m => Options -> TypedModuleFile -> SimplifyM m TypedModuleFile
simplifyModuleFile opts (Left (t,args,m)) = do
    (args',m') <- simplifyModuleWithPPArgs opts (args,m)
    return $ Left (t,args',m')
simplifyModuleFile opts (Right sci) = return $ Right sci

simplifyModuleWithPPArgs :: SimplifyK loc m => Options -> (PPArgs,Module GIdentifier (Typed loc)) -> SimplifyM m (PPArgs,Module GIdentifier (Typed loc))
simplifyModuleWithPPArgs opts (ppargs,x) = liftM (ppargs,) $ simplifyModule opts' x
    where opts' = mappend opts (ppOptions ppargs)

simplifyModule :: Options -> SimplifyG loc m Module
simplifyModule opts m@(Module l n p) = do
    if (simplify opts)
        then do
            when (debugTransformation opts) $ do
                ppm <- ppr (moduleGId m)
                lift $ liftIO $ hPutStrLn stderr ("Simplifying module " ++ ppm ++ "...")
            p' <- simplifyProgram p
            return $ Module l n p'
        else return m

trySimplify :: SimplifyK Position m => (a -> SimplifyM m a) -> (a -> SimplifyM m a)
trySimplify f x = do
    opts <- askOpts
    if simplify opts
        then f x
        else return x

simplifyDecType :: SimplifyK Position m => DecType -> SimplifyM m DecType
simplifyDecType (DecType i isRec ts hd bd specs dec) = do
    dec' <- simplifyInnerDecType dec
    return $ DecType i isRec ts hd bd specs dec'
simplifyDecType d = return d

simplifyInnerDecType :: SimplifyK Position m => InnerDecType -> SimplifyM m InnerDecType
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
    bodyanns' <- concatMapM (procAnn False) bodyanns
    return $ FunType isLeak p pid args ret (anns' ++ bodyanns') body' cl
simplifyInnerDecType (LemmaType isLeak p pid args anns body cl) = do
    anns' <- simplifyProcedureAnns anns
    body' <- mapM (simplifyStatements Nothing) body
    return $ LemmaType isLeak p pid args (anns') body' cl
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
simplifyGlobalDeclaration (GlobalAnnotations l as) = do
    as' <- mapM simplifyGlobalAnn as
    return $ GlobalAnnotations l as'
simplifyGlobalDeclaration g = return g

simplifyGlobalAnn :: SimplifyG loc m GlobalAnnotation
simplifyGlobalAnn (GlobalAxiomAnn l p) = do
    p' <- simplifyAxiomDeclaration p
    return $ GlobalAxiomAnn l p'
simplifyGlobalAnn (GlobalLemmaAnn l p) = do
    p' <- simplifyLemmaDeclaration p
    return $ GlobalLemmaAnn l p'
simplifyGlobalAnn (GlobalFunctionAnn l p) = do
    p' <- simplifyFunctionDeclaration p
    return $ GlobalFunctionAnn l p'
simplifyGlobalAnn (GlobalProcedureAnn l p) = do
    p' <- simplifyProcedureDeclaration p
    return $ GlobalProcedureAnn l p'
simplifyGlobalAnn (GlobalTemplateAnn l p) = do
    p' <- simplifyTemplateDeclaration p
    return $ GlobalTemplateAnn l p'
simplifyGlobalAnn g = return g

simplifyTemplateDeclaration :: SimplifyG loc m TemplateDeclaration
simplifyTemplateDeclaration (TemplateProcedureDeclaration l args p) = do
    p' <- simplifyProcedureDeclaration p
    return $ TemplateProcedureDeclaration l args (addAnnsProcedureDeclaration p' [])
simplifyTemplateDeclaration (TemplateFunctionDeclaration l args p) = do
    p' <- simplifyFunctionDeclaration p
    return $ TemplateFunctionDeclaration l args (addAnnsFunctionDeclaration p' [])
simplifyTemplateDeclaration (TemplateStructureDeclaration l targs s) = do
    s' <- simplifyStructureDeclaration s
    return $ TemplateStructureDeclaration l targs s'
simplifyTemplateDeclaration (TemplateStructureSpecialization l targs tspecs s) = do
    s' <- simplifyStructureDeclaration s
    return $ TemplateStructureSpecialization l targs tspecs s'

simplifyStructureDeclaration :: SimplifyG loc m StructureDeclaration
simplifyStructureDeclaration s = return s

simplifyProcedureDeclaration :: SimplifyG loc m ProcedureDeclaration
simplifyProcedureDeclaration (OperatorDeclaration l ret op args ctx anns body) = do
    (ss0,ret') <- simplifyReturnTypeSpecifier True ret
    (ss1,ctx') <- simplifyTemplateContext ctx
    anns' <- simplifyProcedureAnns anns
    body' <- simplifyStatements Nothing body
    ctxanns <- stmtsAnns (ss0++ss1)
    ctxanns' <- concatMapM (procAnn False) ctxanns
    return (OperatorDeclaration l ret' op args ctx' (anns'++ctxanns') body')
simplifyProcedureDeclaration (ProcedureDeclaration l ret op args ctx anns body) = do
    (ss0,ret') <- simplifyReturnTypeSpecifier True ret
    (ss1,ctx') <- simplifyTemplateContext ctx
    anns' <- simplifyProcedureAnns anns
    body' <- simplifyStatements Nothing body
    ctxanns <- stmtsAnns (ss0++ss1)
    ctxanns' <- concatMapM (procAnn False) ctxanns
    return (ProcedureDeclaration l ret' op args ctx' (anns'++ctxanns') body')

simplifyFunctionDeclaration :: SimplifyG loc m FunctionDeclaration
simplifyFunctionDeclaration (OperatorFunDeclaration l isLeak ret op args ctx anns body) = do
    (ss0,ret') <- simplifyTypeSpecifier True ret
    (ss1,ctx') <- simplifyTemplateContext ctx
    anns' <- simplifyProcedureAnns anns
    (ss,body') <- simplifyNonVoidExpression True body
    bodyanns <- stmtsAnns (ss0++ss1++ss)
    bodyanns' <- concatMapM (procAnn False) bodyanns
    return (OperatorFunDeclaration l isLeak ret' op args ctx' (anns' ++ bodyanns') body')
simplifyFunctionDeclaration (FunDeclaration l isLeak ret op args ctx anns body) = do
    (ss0,ret') <- simplifyTypeSpecifier True ret
    (ss1,ctx') <- simplifyTemplateContext ctx
    anns' <- simplifyProcedureAnns anns
    (ss,body') <- simplifyNonVoidExpression True body
    bodyanns <- stmtsAnns (ss0++ss1++ss)
    bodyanns' <- concatMapM (procAnn False) bodyanns
    return (FunDeclaration l isLeak ret' op args ctx' (anns' ++ bodyanns') body')

simplifyLemmaDeclaration :: SimplifyG loc m LemmaDeclaration
simplifyLemmaDeclaration (LemmaDeclaration l isLeak op qs hctx args bctx anns body) = do
    (ss0,hctx') <- simplifyTemplateContext hctx
    (ss1,bctx') <- simplifyTemplateContext bctx
    anns' <- simplifyProcedureAnns anns
    ctxanns <- stmtsAnns (ss0++ss1)
    ctxanns' <- concatMapM (procAnn False) ctxanns
    body' <- mapM (simplifyStatements Nothing) body
    return $ LemmaDeclaration l isLeak op qs hctx' args bctx' (anns' ++ ctxanns') body'
    
simplifyAxiomDeclaration :: SimplifyG loc m AxiomDeclaration
simplifyAxiomDeclaration (AxiomDeclaration l isLeak op args anns) = do
    anns' <- simplifyProcedureAnns anns
    return $ AxiomDeclaration l isLeak op args (anns' )

simplifyTemplateContext :: SimplifyK loc m => SimplifyCont loc m (TemplateContext GIdentifier (Typed loc))
simplifyTemplateContext (TemplateContext l c) = do
    (ss,c') <- simplifyMaybe (simplifyList (simplifyContextConstraint True)) c
    return (ss,TemplateContext l c')

simplifyContextConstraint :: SimplifyK loc m => Bool -> SimplifyCont loc m (ContextConstraint GIdentifier (Typed loc))
simplifyContextConstraint isExpr (ContextPDec l cl isLeak isAnn ck ret n targs pargs) = do
    (ss1,ret') <- simplifyReturnTypeSpecifier isExpr ret
    (ss2,targs') <- simplifyMaybe (simplifyList (simplifyVariadic (simplifyTemplateTypeArgument isExpr))) targs
    (ss3,pargs') <- simplifyList (simplifyCtxPArg isExpr) pargs
    return (ss1++ss2++ss3,ContextPDec l cl isLeak isAnn ck ret' n targs' pargs')
simplifyContextConstraint isExpr (ContextODec l cl isLeak isAnn ck ret n targs pargs) = do
    (ss1,ret') <- simplifyReturnTypeSpecifier isExpr ret
    (ss2,targs') <- simplifyMaybe (simplifyList (simplifyVariadic (simplifyTemplateTypeArgument isExpr))) targs
    (ss3,pargs') <- simplifyList (simplifyCtxPArg isExpr) pargs
    return (ss1++ss2++ss3,ContextODec l cl isLeak isAnn ck ret' n targs' pargs')
simplifyContextConstraint isExpr (ContextTDec l cl n targs) = do
    (ss1,targs') <- simplifyList (simplifyVariadic (simplifyTemplateTypeArgument isExpr)) targs
    return (ss1,ContextTDec l cl n targs')

simplifyCtxPArg :: SimplifyK loc m => Bool -> SimplifyCont loc m (CtxPArg GIdentifier (Typed loc))
simplifyCtxPArg isExpr (CtxExprPArg l isConst e isVariadic) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
    return (ss,CtxExprPArg l isConst e' isVariadic)
simplifyCtxPArg isExpr (CtxTypePArg l isConst t isVariadic) = do
    (ss,t') <- simplifyTypeSpecifier isExpr t
    return (ss,CtxTypePArg l isConst t' isVariadic)
simplifyCtxPArg isExpr (CtxVarPArg l isConst t isVariadic) = do
    return ([],CtxVarPArg l isConst t isVariadic)

simplifyVariableDeclaration :: SimplifyK loc m => VariableDeclaration GIdentifier (Typed loc) -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyVariableDeclaration (VariableDeclaration l isConst isHavoc t vs) = do
    (xs,t') <- simplifyTypeSpecifier False t
    xs' <- concatMapM (simplifyVariableInitialization isConst t') $ Foldable.toList vs
    return $ xs ++ xs'  
    
simplifyVariableInitialization :: SimplifyK loc m => Bool -> TypeSpecifier GIdentifier (Typed loc) -> VariableInitialization GIdentifier (Typed loc) -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyVariableInitialization isConst t (VariableInitialization l v szs mbe) = do
    (ss,szs') <- simplifyMaybeSizes False szs
    let def = VariableDeclaration l isConst True t $ WrapNe $ VariableInitialization l v szs' Nothing
    ass <- case mbe of
        Nothing -> return []
        Just e -> do
            (ss',e') <- simplifyExpression False e
            let ass' = maybe [] (\e -> [ExpressionStatement l $ BinaryAssign l (varExpr v) (BinaryAssignEqual noloc) e]) e'
            return (ss'++ass')
    return (ss ++ VarStatement l def:ass)

simplifyReturnTypeSpecifier :: Bool -> SimplifyT loc m ReturnTypeSpecifier
simplifyReturnTypeSpecifier isExpr (ReturnType l t) = do
    (ss,t') <- simplifyMaybe (simplifyTypeSpecifier isExpr) t
    return (ss,ReturnType l t')
    
simplifyTypeSpecifier :: Bool -> SimplifyT loc m TypeSpecifier
simplifyTypeSpecifier isExpr (TypeSpecifier l s t d) = do
    (ss,t') <- simplifyDatatypeSpecifier isExpr t
    (ss',d') <- simplifyMaybe (simplifyDimtypeSpecifier isExpr) d
    return (ss++ss',TypeSpecifier l s t' d')

simplifyDimtypeSpecifier :: Bool -> SimplifyT loc m DimtypeSpecifier
simplifyDimtypeSpecifier isExpr (DimSpecifier l e) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
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
simplifyDatatypeSpecifier isExpr (SetSpecifier l b) = do
    (ss,b') <- simplifyDatatypeSpecifier isExpr b
    return (ss,SetSpecifier l b')

simplifyTemplateTypeArgument :: Bool -> SimplifyT loc m TemplateTypeArgument
simplifyTemplateTypeArgument isExpr a@(GenericTemplateTypeArgument l arg) = return ([],a)
simplifyTemplateTypeArgument isExpr a@(TemplateTemplateTypeArgument l n args) = return ([],a)
simplifyTemplateTypeArgument isExpr a@(PrimitiveTemplateTypeArgument {}) = return ([],a)
simplifyTemplateTypeArgument isExpr (ExprTemplateTypeArgument l e) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
    return (ss,ExprTemplateTypeArgument l e')
simplifyTemplateTypeArgument isExpr a@(PublicTemplateTypeArgument {}) = return ([],a)

simplifyMaybeSizes :: Bool -> SimplifyCont loc m (Maybe (Sizes GIdentifier (Typed loc)))
simplifyMaybeSizes isExpr Nothing = return ([],Nothing)
simplifyMaybeSizes isExpr (Just (Sizes es)) = do
    (ss,es') <- simplifyVariadicExpressions isExpr $ Foldable.toList es
    if null es'
        then return (ss,Nothing)
        else return (ss,Just $ Sizes $ fromListNe es')

simplifyExpressions :: SimplifyK loc m => Bool -> [Expression GIdentifier (Typed loc)] -> SimplifyM m ([Statement GIdentifier (Typed loc)],[Expression GIdentifier (Typed loc)])
simplifyExpressions isExpr es = do
    (ss,es') <- Utils.mapAndUnzipM (simplifyExpression isExpr) es
    return (concat ss,map (fromJustNote "simplifyExpressions") es')
    
-- the splitted statements and expression must be pure
simplifyExpression :: SimplifyK loc m => Bool -> Expression GIdentifier (Typed loc) -> SimplifyM m ([Statement GIdentifier (Typed loc)],Maybe (Expression GIdentifier (Typed loc)))
simplifyExpression isExpr (ProcCallExpr l n@(loc -> Typed pl pt) ts es) = do
    (ss,ts') <- simplifyMaybe (simplifyList (simplifyVariadic (simplifyTemplateTypeArgument isExpr))) ts
    (ss',es') <- simplifyVariadicExpressions isExpr es
    mb <- inlineProcCall True isExpr (unTyped l) (fmap (const $ NoType "simpleProc") $ procedureNameId n) pt es'
    case mb of
        Right t' -> return (ss++ss',Just $ ProcCallExpr l (updLoc n $ Typed pl t') ts' es')
        Left (ss'',res) -> return (ss++ss'++ss'',res)
simplifyExpression isExpr e@(BinaryExpr l e1 o@(loc -> Typed ol ot) e2) = do
    (ss1,e1') <- simplifyNonVoidExpression isExpr e1
    (ss2,e2') <- simplifyNonVoidExpression isExpr e2
    mb <- inlineProcCall True isExpr (unTyped l) (OIden $ fmap typed o) ot [(e1',False),(e2',False)]
    case mb of
        Right t' -> return (ss1++ss2,Just $ BinaryExpr l e1' (updLoc o $ Typed ol t') e2')
        Left (ss3,res) -> return (ss1++ss2++ss3,res)
simplifyExpression isExpr (UnaryExpr l o@(loc -> Typed ol ot) e) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
    mb <- inlineProcCall True isExpr (unTyped l) (OIden $ fmap typed o) ot [(e',False)]
    case mb of
        Right t' -> return (ss,Just $ UnaryExpr l (updLoc o $ Typed ol t') e')
        Left (ss',res) -> return (ss++ss',res)
simplifyExpression isExpr (CondExpr l c e1 e2) = do
    (ssc,c') <- simplifyNonVoidExpression isExpr c
    (ss1,e1') <- withCondExpr c' $ simplifyNonVoidExpression isExpr e1
    (ss2,e2') <- withCondExpr (negBoolExprLoc c') $ simplifyNonVoidExpression isExpr e2
    return (ssc++ss1++ss2,Just $ CondExpr l c' e1' e2')
simplifyExpression isExpr (BinaryAssign l e1 bop e2) = do
    let mb_op = binAssignOpToOp bop
    (ss,e2') <- case mb_op of
        Just op -> simplifyNonVoidExpression isExpr (BinaryExpr l e1 op e2)
        Nothing -> simplifyNonVoidExpression isExpr e2
    return (ss,Just $ BinaryAssign l e1 (BinaryAssignEqual l) e2')
simplifyExpression isExpr (PostIndexExpr l e s) = do
    (ss1,e') <- simplifyNonVoidExpression isExpr e
    (ss2,s') <- simplifySubscript isExpr s
    let stay = do
        let pe' = PostIndexExpr l e' s'
        return (ss1++ss2,Just pe')
    case e' of
        ArrayConstructorPExpr {} -> do
            let go = do
                let tl = unTyped l
                e'' <- liftM (fmap (Typed tl)) $ projectArrayExpr tl (fmap typed e') (map (fmap typed) $ Foldable.toList s)
                return (ss1++ss2,Just e'')
            catchError go (\err -> stay)
        otherwise -> stay
            
simplifyExpression isExpr (QualExpr l e t) = do
    (sse,e') <- simplifyNonVoidExpression isExpr e
    (sst,t') <- simplifyTypeSpecifier isExpr t
    return (sse++sst,Just $ QualExpr l e' t')
simplifyExpression isExpr (SelectionExpr l e att) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
    return (ss,Just $ SelectionExpr l e' att)
simplifyExpression isExpr (ToMultisetExpr l e) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
    return (ss,Just $ ToMultisetExpr l e')
simplifyExpression isExpr (ToSetExpr l e) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
    return (ss,Just $ ToSetExpr l e')
simplifyExpression isExpr (SetComprehensionExpr l t x px fx) = do
    (ss1,[(t',x')]) <- simplifyQuantifierArgs [(t,x)]
    (ss3,px') <- simplifyNonVoidExpression isExpr px
    (ss4,fx') <- simplifyMaybe (simplifyNonVoidExpression isExpr) fx
    return (ss1++ss3++ss4,Just $ SetComprehensionExpr l t' x' px' fx')
simplifyExpression isExpr (ToVArrayExpr l e i) = do
    (ss1,e') <- simplifyNonVoidExpression isExpr e
    (ss2,i') <- simplifyNonVoidExpression isExpr i
    return (ss1++ss2,Just $ ToVArrayExpr l e' i')
simplifyExpression isExpr (BuiltinExpr l n es) = do
    (ss,es') <- simplifyVariadicExpressions isExpr es
    return (ss,Just $ BuiltinExpr l n es')
simplifyExpression isExpr (LeakExpr l e) = do
    (ss,e') <- simplifyNonVoidExpression isExpr e
    return (ss,Just $ LeakExpr l e')
simplifyExpression isExpr (QuantifiedExpr l q args e) = do
    (argsc,args') <- simplifyQuantifierArgs args
    (sse,e') <- simplifyNonVoidExpression True e
    ssq <- stmtsAnns (argsc ++ sse)
    let (map fst -> pre,map fst -> post) = List.partition snd $ map stmtAnnExpr ssq
    return (sse,Just $ QuantifiedExpr l q args $ impliesExprLoc (andExprsLoc pre) $ andExprsLoc $ post++[e'])
simplifyExpression isExpr e = return ([],Just e)

simplifyQuantifierArgs :: SimplifyK loc m => [(TypeSpecifier GIdentifier (Typed loc),VarName GIdentifier (Typed loc))] -> SimplifyM m ([Statement GIdentifier (Typed loc)],[(TypeSpecifier GIdentifier (Typed loc),VarName GIdentifier (Typed loc))])
simplifyQuantifierArgs [] = return ([],[])
simplifyQuantifierArgs (v:vs) = do
    (vc,v') <- simplifyQuantifierArg v
    (vcs,vs') <- simplifyQuantifierArgs vs
    return (vc++vcs,v':vs')

simplifyQuantifierArg :: SimplifyK loc m => (TypeSpecifier GIdentifier (Typed loc),VarName GIdentifier (Typed loc)) -> SimplifyM m ([Statement GIdentifier (Typed loc)],(TypeSpecifier GIdentifier (Typed loc),VarName GIdentifier (Typed loc)))
simplifyQuantifierArg (t,v) = do
    (sst,t') <- simplifyTypeSpecifier True t
    return (sst,(t',v))

simplifyNonVoidExpression :: Bool -> SimplifyT loc m Expression
simplifyNonVoidExpression isExpr e = do
    (ss,mbe') <- simplifyExpression isExpr e
    case mbe' of
        Just e' -> return (ss,e')
        Nothing -> return ([],e)

simplifySubscript :: Bool -> SimplifyT loc m Subscript
simplifySubscript isExpr es = do
    (ss,es') <- Utils.mapAndUnzipM (simplifyIndex isExpr) es
    return (concat $ Foldable.toList ss,es')

simplifyIndex :: Bool -> SimplifyT loc m Index
simplifyIndex isExpr (IndexInt l e) = do
    (ss,Just e') <- simplifyExpression isExpr e
    return (ss,IndexInt l e')
simplifyIndex isExpr (IndexSlice l e1 e2) = do
    (ss1,e1') <- simplifyMaybe (simplifyNonVoidExpression isExpr) e1
    (ss2,e2') <- simplifyMaybe (simplifyNonVoidExpression isExpr) e2
    return (ss1++ss2,IndexSlice l e1' e2')

unfoldVariadicExpr :: SimplifyK loc m => (Expression GIdentifier (Typed loc),IsVariadic) -> TcM m [Expression GIdentifier (Typed loc)]
unfoldVariadicExpr (e,isVariadic) = do
    let Typed l t = loc e
    es <- expandVariadicExpr l False (fmap typed e,isVariadic)
    return $ map (fmap $ Typed l) es

bindProcArgs :: SimplifyK loc m => Bool -> loc -> [(Bool,Var,IsVariadic)] -> [Expression GIdentifier (Typed loc)] -> SimplifyM m ([Statement GIdentifier (Typed loc)],Map GIdentifier (Expression GIdentifier (Typed loc)))
bindProcArgs isExpr l [] [] = return ([],Map.empty)
bindProcArgs isExpr l (v:vs) es = do
    (es',ss,substs) <- bindProcArg isExpr l v es
    (ss',substs') <- bindProcArgs isExpr l vs es'
    return (ss++ss',Map.union substs substs')

bindProcArg :: SimplifyK loc m => Bool -> loc -> (Bool,Var,IsVariadic) -> [Expression GIdentifier (Typed loc)] -> SimplifyM m ([Expression GIdentifier (Typed loc)],[Statement GIdentifier (Typed loc)],Map GIdentifier (Expression GIdentifier (Typed loc)))
bindProcArg False l (False,v,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier False t
    let tl = notTyped "bind" l
    let def = VarStatement tl $ VariableDeclaration tl False True t' $ WrapNe $ VariableInitialization tl (fmap (Typed l) v) Nothing $ Just e
    return (es,ss1++[def],Map.empty)
bindProcArg True l (False,v,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier True t
    let tl = notTyped "bind" l
    return (es,ss1,Map.singleton (varNameId v) e)
bindProcArg False l (True,v,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    --(ss1,t') <- simplifyTypeSpecifier False t
    let tl = notTyped "bind" l
    --let def = VarStatement tl $ VariableDeclaration tl True True t' $ WrapNe $ VariableInitialization tl (fmap (Typed l) v) Nothing $ Just e
    return (es,[],Map.singleton (varNameId v) e)
bindProcArg True l (True,v,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    let tl = notTyped "bind" l
    return (es,[],Map.singleton (varNameId v) e)
bindProcArg isExpr l (_,v,True) es = do
    sz <- fullyEvaluateIndexExpr (locpos l) =<< typeSize (locpos l) (loc v)
    let (es1,es2) = splitAt (fromEnum sz) es
    return (es2,[],Map.singleton (varNameId v) $ ArrayConstructorPExpr (Typed l $ loc v) es1)

simplifyProcedureAnns :: SimplifyK loc m => [ProcedureAnnotation GIdentifier (Typed loc)] -> SimplifyM m [ProcedureAnnotation GIdentifier (Typed loc)]
simplifyProcedureAnns = liftM concat . mapM simplifyProcedureAnn

simplifyProcedureAnn :: SimplifyK loc m => ProcedureAnnotation GIdentifier (Typed loc) -> SimplifyM m [ProcedureAnnotation GIdentifier (Typed loc)]
simplifyProcedureAnn (RequiresAnn l isFree isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- stmtsAnns ss
    anns' <- concatMapM (procAnn False) anns
    return $ anns' ++ [RequiresAnn l isFree isLeak e']
simplifyProcedureAnn (EnsuresAnn l isFree isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- stmtsAnns ss
    anns' <- concatMapM (procAnn True) anns
    return $ anns' ++ [EnsuresAnn l isFree isLeak e']
simplifyProcedureAnn a@(InlineAnn l isInline) = return [a]
simplifyProcedureAnn (PDecreasesAnn l e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- stmtsAnns ss
    anns' <- concatMapM (procAnn False) anns
    return $ anns' ++ [PDecreasesAnn l e']

procAnn :: ProverK loc m => Bool -> StatementAnnotation GIdentifier (Typed loc) -> SimplifyM m [ProcedureAnnotation GIdentifier (Typed loc)]
procAnn isPost s = procAnn' isPost False s

procAnn' :: ProverK loc m => Bool -> Bool -> StatementAnnotation GIdentifier (Typed loc) -> SimplifyM m [ProcedureAnnotation GIdentifier (Typed loc)]
procAnn' True l1 (AssertAnn l isLeak e) = return [EnsuresAnn l False (l1 || isLeak) e]
procAnn' True l1 (AssumeAnn l isLeak e) = return [EnsuresAnn l True (l1 || isLeak) e]
procAnn' False l1 (AssertAnn l isLeak e) = return [RequiresAnn l False (l1 || isLeak) e]
procAnn' False l1 (AssumeAnn l isLeak e) = return [RequiresAnn l True (l1 || isLeak) e]
procAnn' isPost l1 (EmbedAnn l isLeak s) = do
    as <- stmtAnns s
    concatMapM (procAnn' isPost (l1 || isLeak)) as

splitProcAnns :: ProverK loc m => [ProcedureAnnotation iden (Typed loc)] -> SimplifyM m ([StatementAnnotation iden (Typed loc)],[StatementAnnotation iden (Typed loc)])
splitProcAnns [] = return ([],[])
splitProcAnns (RequiresAnn p isFree isLeak e:xs) = do
    (l,r) <- splitProcAnns xs
    let k = if isFree then AssumeAnn else AssertAnn
    return (k p isLeak e:l,r)
splitProcAnns (EnsuresAnn p isFree isLeak e:xs) = do
    (l,r) <- splitProcAnns xs
    let k = if isFree then AssumeAnn else AssertAnn
    return (l,k p isLeak e:r)
splitProcAnns (InlineAnn {}:xs) = splitProcAnns xs
splitProcAnns (PDecreasesAnn {}:xs) = splitProcAnns xs

simplifyStatementAnns :: SimplifyK loc m => Bool -> [StatementAnnotation GIdentifier (Typed loc)] -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyStatementAnns isExpr = liftM concat . mapM (simplifyStatementAnn isExpr)

simplifyStatementAnn :: SimplifyK loc m => Bool -> StatementAnnotation GIdentifier (Typed loc) -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyStatementAnn isExpr (AssumeAnn l isLeak e) = do
    (ss,Just e') <- simplifyExpression isExpr e
    let ss' = makeAnnStmts (unTyped l) isLeak ss
    return $ ss' ++ annStmts (unTyped l) [AssumeAnn l isLeak e']
simplifyStatementAnn isExpr (AssertAnn l isLeak e) = do
    (ss,Just e') <- simplifyExpression isExpr e
    let ss' = makeAnnStmts (unTyped l) isLeak ss
    return $ ss' ++ annStmts (unTyped l) [AssertAnn l isLeak e']
simplifyStatementAnn isExpr (EmbedAnn l isLeak e) = do
    (ss) <- simplifyStatement Nothing e
    let ss' = makeAnnStmts (unTyped l) isLeak ss
    return $ ss'

makeAnnStmts :: Location loc => loc -> Bool -> [Statement GIdentifier (Typed loc)] -> [Statement GIdentifier (Typed loc)]
makeAnnStmts l isLeak = concatMap (makeAnnStmt l isLeak)

makeAnnStmt :: Location loc => loc -> Bool -> Statement GIdentifier (Typed loc) -> [Statement GIdentifier (Typed loc)]
makeAnnStmt l isLeak s = maybeToList $ annStmtMb l [EmbedAnn (notTyped "makeAnn" l) isLeak s]

simplifyLoopAnns :: SimplifyK loc m => [LoopAnnotation GIdentifier (Typed loc)] -> SimplifyM m [LoopAnnotation GIdentifier (Typed loc)]
simplifyLoopAnns = liftM concat . mapM simplifyLoopAnn

simplifyLoopAnn :: SimplifyK loc m => LoopAnnotation GIdentifier (Typed loc) -> SimplifyM m [LoopAnnotation GIdentifier (Typed loc)]
simplifyLoopAnn (InvariantAnn l isFree isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- liftM (map stmtAnn2LoopAnn) (stmtsAnns ss)
    return $ anns ++ [InvariantAnn l isFree isLeak e']
simplifyLoopAnn (DecreasesAnn l isLeak e) = do
    (ss,Just e') <- simplifyExpression True e
    anns <- liftM (map stmtAnn2LoopAnn) (stmtsAnns ss)
    return $ anns ++ [DecreasesAnn l isLeak e']

stmtsAnns :: (PP (TcM m) iden,SimplifyK loc m) => [Statement iden (Typed loc)] -> SimplifyM m [StatementAnnotation iden (Typed loc)]
stmtsAnns = liftM concat . mapM stmtAnns

stmtAnns :: (PP (TcM m) iden,SimplifyK loc m) => Statement iden (Typed loc) -> SimplifyM m [StatementAnnotation iden (Typed loc)]
stmtAnns (AnnStatement _ anns) = return anns
stmtAnns (CompoundStatement _ ss) = stmtsAnns ss
stmtAnns s = do
    pps <- pp s
    genError (locpos $ loc s) $ text "expected an annotation but found statement" <+> pps

stmtAnnExpr :: StatementAnnotation iden (Typed loc) -> (Expression iden (Typed loc),Bool)
stmtAnnExpr (AssumeAnn _ isLeak e) = (e,True)
stmtAnnExpr (AssertAnn _ isLeak e) = (e,False)

stmtAnn2LoopAnn :: StatementAnnotation iden (Typed loc) -> LoopAnnotation iden (Typed loc)
stmtAnn2LoopAnn (AssumeAnn l isLeak e) = InvariantAnn l True isLeak e
stmtAnn2LoopAnn (AssertAnn l isLeak e) = InvariantAnn l False isLeak e

loopAnn2StmtAnn :: LoopAnnotation iden (Typed loc) -> StatementAnnotation iden (Typed loc)
loopAnn2StmtAnn (InvariantAnn l True isLeak e) = AssumeAnn l isLeak e
loopAnn2StmtAnn (InvariantAnn l False isLeak e) = AssertAnn l isLeak e

tryInlineExpr :: SimplifyK loc m => loc -> Expr -> SimplifyM m (Maybe Expr)
tryInlineExpr l ue@(UnaryExpr ret o e) = do
    mb <- inlineProcCall True True l (OIden o) (loc o) [(fmap (Typed l) e,False)]
    case mb of
        Left (_,Just e) -> do
            return $ Just $ fmap typed e
        otherwise -> return Nothing
tryInlineExpr l ue@(BinaryExpr ret e1 o e2) = do
    mb <- inlineProcCall True True l (OIden o) (loc o) [(fmap (Typed l) e1,False),(fmap (Typed l) e2,False)]
    case mb of
        Left (_,Just e) -> do
            return $ Just $ fmap typed e
        otherwise -> return Nothing
tryInlineExpr l ue@(ProcCallExpr ret p@(ProcedureName ln (PIden pn)) ts es) = do
    mb <- inlineProcCall True True l (PIden pn) (loc p) (map (mapFst (fmap (Typed l))) es)
    case mb of
        Left (_,Just e) -> do
            return $ Just $ fmap typed e
        otherwise -> return Nothing
tryInlineExpr l e = return Nothing

inlineExpr :: SimplifyK loc m => loc -> Expr -> SimplifyM m Expr
inlineExpr l e = do
    mb <- tryInlineExpr l e
    case mb of
        Just e -> return e
        Nothing -> do
            ppe <- pp e
            ppd <- pp (loc e)
            tcError (locpos l) $ Halt $ GenTcError (text "cannot inline expression" <+> ppe <+> ppd) Nothing

tryInlineLemmaCall :: SimplifyK loc m => loc -> Expression GIdentifier (Typed loc) -> SimplifyM m (Maybe (Maybe DecType,[StatementAnnotation GIdentifier (Typed loc)]))
tryInlineLemmaCall l (ProcCallExpr _ (ProcedureName (Typed _ (DecT dec)) (PIden n)) targs args) | decTyKind dec == LKind = do
    let dec' = chgDecInline True dec
    mb <- inlineProcCall False False l (PIden n) (DecT dec') args
    case mb of
        Left (ss,Nothing) -> do
            anns <- stmtsAnns ss
            case lemmaDecBody dec of
                Nothing -> return $ Just (Nothing,anns)
                Just _ -> return $ Just (Just dec,anns)
        otherwise -> return Nothing
tryInlineLemmaCall l e = return Nothing

-- inlines a procedures
-- we assume that typechecking has already tied the procedure's type arguments
inlineProcCall :: SimplifyK loc m => Bool -> Bool -> loc -> PIdentifier -> Type -> [(Expression GIdentifier (Typed loc),IsVariadic)] -> SimplifyM m (Either ([Statement GIdentifier (Typed loc)],Maybe (Expression GIdentifier (Typed loc))) Type)
inlineProcCall withBody isExpr l n t@(DecT d) es = do
    mbes' <- tryTcError l $ concatMapM unfoldVariadicExpr es
    case mbes' of
        Right es' -> readable1 (inlineProcCall' es') l d
        Left _ -> do
            d' <- simplifyDecType d
            debugTc $ do
                ppn <- ppr n
                ppes <- ppr es
                ppd' <- ppr d'
                liftIO $ putStrLn $ "not inline parameters" ++ pprid isExpr ++ " " ++ ppn ++ " " ++ ppes ++ " " ++ ppd'
            return $ Right $ DecT d'
  where
    inlineProcCall' es' (DecType _ _ _ _ _ _ (LemmaType _ _ _ args ann (Just body) c)) | withBody && not isExpr && isInlineDecClass c = do
        debugTc $ do
            ppn <- ppr n
            ppes <- ppr es
            ppt <- ppr t
            liftIO $ putStrLn $ "inlineLemmaFalse " ++ ppn ++ " " ++ ppes ++ " " ++ ppt
        
        (decls,substs) <- bindProcArgs False l args es'
        ann' <- subst "inlineLemmaCall" dontStop (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) ann
        body' <- subst "inlineLemmaCall" dontStop (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) body
        (reqs,ens) <- splitProcAnns ann'
        reqs' <- simplifyStatementAnns True reqs
        ss <- simplifyStatements Nothing body'
        ens' <- simplifyStatementAnns True ens
        return $ Left (compoundStmts l (decls++reqs'++ss++ens'),Nothing)
    inlineProcCall' es' (DecType _ _ _ _ _ _ (LemmaType _ _ _ args ann _ c)) | not withBody && not isExpr && isInlineDecClass c = do
        debugTc $ do
            ppn <- ppr n
            ppes <- ppr es
            ppt <- ppr t
            liftIO $ putStrLn $ "inlineLemmaFalse " ++ ppn ++ " " ++ ppes ++ " " ++ ppt
        ([],substs) <- bindProcArgs True l args es'
        ann' <- subst "inlineLemmaCall" dontStop (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) ann
        (reqs,ens) <- splitProcAnns ann'
        reqs' <- simplifyStatementAnns True reqs
        ens' <- simplifyStatementAnns True ens
        return $ Left (compoundStmts l (reqs'++ens'),Nothing)
    inlineProcCall' es' (DecType _ _ _ _ _ _ (ProcType _ _ args ret ann (Just body) c)) | not isExpr && isInlineDecClass c = do
        debugTc $ do
            ppn <- ppr n
            ppes <- ppr es
            ppt <- ppr t
            liftIO $ putStrLn $ "inlineProcFalse " ++ ppn ++ " " ++ ppes ++ " " ++ ppt
        (decls,substs) <- bindProcArgs False l args es'
        ann' <- subst "inlineProcCall" dontStop (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) ann
        body' <- subst "inlineProcCall" dontStop (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) body
        mb <- type2TypeSpecifier l ret
        case mb of
            Just t -> do
                res <- liftM (VarName (Typed l ret)) $ genVar (VIden $ mkVarId "res" :: GIdentifier)
                let ssres = Map.singleton (VIden $ mkVarId "\\result" :: GIdentifier) (varExpr res)
                ann'' <- subst "inlineProcCall" dontStop (substsFromMap ssres) False Map.empty ann'
                (reqs,ens) <- splitProcAnns ann''
                (ss1,t') <- simplifyTypeSpecifier False t
                let tl = notTyped "inline" l
                let def = VarStatement tl $ VariableDeclaration tl False True t' $ WrapNe $ VariableInitialization tl res Nothing Nothing
                reqs' <- simplifyStatementAnns True reqs
                ss <- simplifyStatements (Just res) body'
                debugTc $ do
                    ppn <- ppr n
                    ppres <- ppr res
                    ppss <- liftM vcat $ mapM pp ss
                    liftIO $ putStrLn $ "inlineProcCall return " ++ ppn ++ " " ++ ppres ++ "\n" ++ show ppss
                ens' <- simplifyStatementAnns True ens
                return $ Left (decls++ss1++[def] ++ compoundStmts l (reqs'++ss++ens'),Just $ varExpr res)
            Nothing -> do
                (reqs,ens) <- splitProcAnns ann'
                reqs' <- simplifyStatementAnns True reqs
                ss <- simplifyStatements Nothing body'
                ens' <- simplifyStatementAnns True ens
                return $ Left (compoundStmts l (decls++reqs'++ss++ens'),Nothing)
    inlineProcCall' es' (DecType _ _ _ _ _ _ (FunType isLeak _ _ args ret ann (Just body) c)) | not isExpr && isInlineDecClass c = do
        debugTc $ do
            ppn <- ppr n
            ppes <- ppr es
            ppt <- ppr t
            liftIO $ putStrLn $ "inlineFunFalse " ++ ppn ++ " " ++ ppes ++ " " ++ ppt
        (decls,substs) <- bindProcArgs False l args es'
        res <- liftM (VarName (Typed l ret)) $ genVar (VIden $ mkVarId "res")
        let ssres = Map.singleton (VIden $ mkVarId "\\result") (varExpr res)
        ann' <- subst "inlineFunFalse" dontStop (substsFromMap $ Map.union substs ssres) False Map.empty $ map (fmap (fmap (updpos l))) ann
        body' <- subst "inlineFunFalse" dontStop (substsFromMap substs) False Map.empty $ fmap (fmap (updpos l)) body
        t <- type2TypeSpecifierNonVoid l ret
        (reqs,ens) <- splitProcAnns ann'
        (ss1,t') <- simplifyTypeSpecifier False t
        let tl = notTyped "inline" l
        let def = VarStatement tl $ VariableDeclaration tl False True t' $ WrapNe $ VariableInitialization tl res Nothing Nothing
        reqs' <- simplifyStatementAnns True reqs
        (ss,Just body'') <- simplifyExpression False body'
        let sbody = [ExpressionStatement tl $ BinaryAssign (loc res) (varExpr res) (BinaryAssignEqual tl) body'']
        ens' <- simplifyStatementAnns True ens
        return $ Left (decls++ss1++[def] ++ compoundStmts l (reqs'++ss++sbody++ens'),Just $ varExpr res)
    inlineProcCall' es' (DecType _ _ _ _ _ _ (FunType isLeak _ _ args ret ann (Just body) c)) | isExpr && isInlineDecClass c = do
        debugTc $ do
            ppn <- ppr n
            ppes <- ppr es
            ppt <- ppr t
            liftIO $ putStrLn $ "inlineFunTrue " ++ ppn ++ " " ++ ppes ++ " " ++ ppt
        (decls,substs) <- bindProcArgs True l args es'
        body' <- subst "inlineFunTrue" dontStop (substsFromMap substs) False Map.empty $ fmap (fmap (updpos l)) body
        (ss,Just body'') <- simplifyExpression True body'
        let ssret = Map.singleton (VIden $ mkVarId "\\result") body''
        ann' <- subst "inlineFunTrue" dontStop (substsFromMap $ Map.union substs ssret) False Map.empty $ map (fmap (fmap (updpos l))) ann
        t <- type2TypeSpecifierNonVoid l ret
        (reqs,ens) <- splitProcAnns ann'
        (ss1,t') <- simplifyTypeSpecifier True t
        let tl = notTyped "inline" l
        reqs' <- simplifyStatementAnns True reqs >>= stmtsAnns
        ens' <- simplifyStatementAnns True ens >>= stmtsAnns
        debugTc $ do
            ppn <- ppr n
            ppes <- ppr es
            ppb' <- ppr body''
            liftIO $ putStrLn $ "inlinedFunTrue " ++ ppn ++ " " ++ ppes ++ " " ++ ppb'
        return $ Left (decls++ss1++compoundStmts l (annStmts l reqs'++ss++annStmts l ens'),Just body'')
    inlineProcCall' es' d = do
        d' <- simplifyDecType d
        debugTc $ do
            ppn <- ppr n
            ppes <- ppr es
            ppd' <- ppr d'
            liftIO $ putStrLn $ "not inline " ++ pprid isExpr ++ " " ++ ppn ++ " " ++ ppes ++ " " ++ ppd'
        return $ Right $ DecT d'

simplifyStmts :: SimplifyK loc m => Maybe (VarName GIdentifier (Typed loc)) -> [Statement GIdentifier (Typed loc)] -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyStmts ret ss = do
    opts <- askOpts
    if simplify opts
        then simplifyStatements ret ss
        else return ss

simplifyStatements :: SimplifyK loc m => Maybe (VarName GIdentifier (Typed loc)) -> [Statement GIdentifier (Typed loc)] -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyStatements ret [] = return []
simplifyStatements ret [s] = simplifyStatement ret s
simplifyStatements ret (s1:s2:ss) = do
    ss1 <- simplifyStatement Nothing s1
    ss2 <- simplifyStatements ret (s2:ss)
    return (ss1++ss2)

simplifyStatement :: SimplifyK loc m => Maybe (VarName GIdentifier (Typed loc)) -> Statement GIdentifier (Typed loc) -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyStatement ret (CompoundStatement l ss) = do
    ss' <- simplifyStatements ret ss
    if null ss' then return [] else return [CompoundStatement l ss']
simplifyStatement ret (IfStatement l c s1 s2) = do
    (ss,c') <- simplifyNonVoidExpression False c
    s1' <- simplifyStatement ret s1
    s2' <- simplifyStatements ret $ maybeToList s2
    return $ (ss++[IfStatement l c' (compoundStmt (unTyped l) s1') (compoundStmtMb (unTyped l) s2')])
simplifyStatement Nothing (ReturnStatement l Nothing) = return [ReturnStatement l Nothing]
simplifyStatement Nothing (ReturnStatement l (Just e)) = do
    (ss,e') <- simplifyNonVoidExpression False e
    return $ ss++[ReturnStatement l (Just e')]
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
    case (ret,e') of
        (Just v,Just e') -> do
            let s' = [ExpressionStatement l $ BinaryAssign (loc v) (varExpr v) (BinaryAssignEqual l) e']
            return (ss++s')
        (Nothing,Just e') -> do
            let s' = [ExpressionStatement l e']
            return (ss++s')
        (Nothing,Nothing) -> return ss
simplifyStatement ret (VarStatement l v) = do
    simplifyVariableDeclaration v
simplifyStatement ret (WhileStatement l c ann s) = do
    (ss,c') <- simplifyNonVoidExpression True c
    anns <- liftM (map stmtAnn2LoopAnn) (stmtsAnns ss)
    ann' <- simplifyLoopAnns (anns++ann)
    s' <- simplifyStatement ret s
    return [WhileStatement l c' ann' $ compoundStmt (unTyped l) s']
--simplifyStatement ret (WhileStatement l c ann s) = do
--    ann' <- simplifyLoopAnns ann
--    let assertinv = AnnStatement l $ map loopAnn2StmtAnn ann'
--    let p = unTyped l
--    let tl = notTyped "inline" p
--    let ty = loc c
--    t' <- type2TypeSpecifierNonVoid p $ typed ty
--    wcond <- liftM (VarName ty) $ genVar (mkVarId "wcond")
--    let def = VarStatement tl $ VariableDeclaration tl t' $ WrapNe $ VariableInitialization tl wcond Nothing Nothing
--    let assign = ExpressionStatement l $ BinaryAssign (loc wcond) (varExpr wcond) (BinaryAssignEqual l) c
--    let ifbreak = IfStatement tl (negBoolExprLoc $ varExpr wcond) (compoundStmtMb (unTyped l) [assertinv,BreakStatement tl]) Nothing
--    s' <- simplifyStatement ret $ compoundStmtMb (unTyped l) $ [assign,ifbreak,s,assertinv]
--    return [def,assertinv,WhileStatement l (fmap (Typed p) trueExpr) [] $ compoundStmtMb (unTyped l) s']
simplifyStatement ret (ForStatement l e c i ann s) = do
    ss <- simplifyForInitializer e
    (ssc,c') <- simplifyMaybe (simplifyNonVoidExpression True) c
    let ic' = case c' of
                Nothing -> fmap (Typed $ unTyped l) trueExpr
                Just c' -> c'
    (ssi,i') <- simplifyMaybe (simplifyNonVoidExpression False) i
    let ie' = case i' of
                Nothing -> []
                Just i' -> [ExpressionStatement l i']
    annsc <- liftM (map stmtAnn2LoopAnn) (stmtsAnns ssc)
    ann' <- simplifyLoopAnns $ annsc++ann
    s' <- simplifyStatement ret s
    return (ss++[WhileStatement l ic' ann' $ compoundStmt (unTyped l) (s'++ ssi ++ ie') ])
simplifyStatement ret (DowhileStatement l ann s c) = do
    ann' <- simplifyLoopAnns ann
    s' <- simplifyStatement ret s
    (ss,Just c') <- simplifyExpression False c
    return [DowhileStatement l ann' (compoundStmt (unTyped l) $ s'++ss) c']
simplifyStatement ret (PrintStatement l es) = do
    (ss,es') <- simplifyVariadicExpressions False es
    return (ss++[PrintStatement l es'])
simplifyStatement ret (AnnStatement l anns) = do
    anns' <- simplifyStatementAnns True anns
    return anns'
simplifyStatement ret (SyscallStatement l n es) = do
    (ss,es') <- Utils.mapAndUnzipM simplifySyscallParameter es
    return $ concat ss ++ [SyscallStatement l n $ concat es']
simplifyStatement ret s = return [s]

simplifySyscallParameter :: SimplifyK loc m => SyscallParameter GIdentifier (Typed loc) -> SimplifyM m ([Statement GIdentifier (Typed loc)],[SyscallParameter GIdentifier (Typed loc)])
simplifySyscallParameter (SyscallPush l e) = do
    (ss,e') <- simplifyVariadicExpression False e
    return (ss,map mkSysPush e')
simplifySyscallParameter (SyscallReturn l v) = return ([],[SyscallReturn l v])
simplifySyscallParameter (SyscallPushRef l v) = return ([],[SyscallPushRef l v])
simplifySyscallParameter (SyscallPushCRef l e) = do
    (ss,e') <- simplifyNonVoidExpression False e
    return (ss,[SyscallPushCRef l e'])

mkSysPush :: Location loc => (Expression GIdentifier (Typed loc),IsVariadic) -> SyscallParameter GIdentifier (Typed loc)
mkSysPush (e,isV) = SyscallPush (Typed l $ SysT $ SysPush t) (e,isV)
    where (Typed l t) = loc e

simplifyForInitializer :: SimplifyK loc m => ForInitializer GIdentifier (Typed loc) -> SimplifyM m [Statement GIdentifier (Typed loc)]
simplifyForInitializer i@(InitializerExpression Nothing) = return []
simplifyForInitializer (InitializerExpression (Just e)) = do
    (ss,e') <- simplifyExpression False e
    let s' = maybe [] (\e -> [ExpressionStatement (loc e) e]) e'
    return (ss++s')
simplifyForInitializer (InitializerVariable vd) = do
    simplifyVariableDeclaration vd

simplifyList :: SimplifyCont loc m a -> SimplifyCont loc m [a]
simplifyList m xs = do
    (ss,xs') <- Utils.mapAndUnzipM m xs
    return (concat ss,xs')

simplifyVariadic :: SimplifyCont loc m a -> SimplifyCont loc m (a,IsVariadic)
simplifyVariadic m (x,isVariadic) = do
    (ss,x') <- m x
    return (ss,(x',isVariadic))

simplifyVariadicExpressions :: Bool -> SimplifyCont loc m [(Expression GIdentifier (Typed loc),IsVariadic)]
simplifyVariadicExpressions isExpr es = do
    (ss,es') <- Utils.mapAndUnzipM (simplifyVariadicExpression isExpr) es
    return (concat ss,concat es')

simplifyVariadicExpression :: SimplifyK loc m => Bool -> (Expression GIdentifier (Typed loc),IsVariadic) -> SimplifyM m ([Statement GIdentifier (Typed loc)],[(Expression GIdentifier (Typed loc),IsVariadic)])
simplifyVariadicExpression isExpr (e,isVariadic) = do
    (ss,Just e') <- simplifyExpression isExpr e
    case (e',isVariadic) of
        (ArrayConstructorPExpr l es,True) -> return (ss,map (,False) es)
        p -> return (ss,[p])
        
simplifyMaybe :: SimplifyCont loc m a -> SimplifyCont loc m (Maybe a) 
simplifyMaybe m Nothing = return ([],Nothing)
simplifyMaybe m (Just x) = do
    (ss,x') <- m x
    return (ss,Just x')

simplifySizes :: Bool -> SimplifyCont loc m (Maybe (Sizes GIdentifier (Typed loc)))
simplifySizes isExpr = simplifyMaybe $ \(Sizes xs) -> do
    (ss,xs') <- simplifyVariadicExpressions isExpr (Foldable.toList xs)
    return (ss,Sizes $ fromListNe xs')

-- * Simplify statement blocks


