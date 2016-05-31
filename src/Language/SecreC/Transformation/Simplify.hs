{-# LANGUAGE TupleSections, ConstraintKinds, ViewPatterns, FlexibleContexts, RankNTypes #-}

module Language.SecreC.Transformation.Simplify where

import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Conversion
import Language.SecreC.TypeChecker.Base
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

simplifyProgram :: SimplifyG loc m Program
simplifyProgram (Program l is gs) = do
    gs' <- mapM simplifyGlobalDeclaration gs
    return $ Program l is gs'

simplifyGlobalDeclaration :: SimplifyG loc m GlobalDeclaration
simplifyGlobalDeclaration (GlobalProcedure l p) = do
    p' <- simplifyProcedureDeclaration p
    return $ GlobalProcedure l p'
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
simplifyTemplateDeclaration (TemplateStructureDeclaration l targs s) = do
    s' <- simplifyStructureDeclaration s
    return $ TemplateStructureDeclaration l targs s'
simplifyTemplateDeclaration (TemplateStructureSpecialization l targs tspecs s) = do
    s' <- simplifyStructureDeclaration s
    return $ TemplateStructureSpecialization l targs tspecs s'

simplifyStructureDeclaration :: SimplifyG loc m StructureDeclaration
simplifyStructureDeclaration s = return s

simplifyProcedureDeclaration :: SimplifyG loc m ProcedureDeclaration
simplifyProcedureDeclaration (OperatorDeclaration l ret op args ann body) = do
    body' <- simplifyStatements Nothing body
    return $ OperatorDeclaration l ret op args ann body'
simplifyProcedureDeclaration (ProcedureDeclaration l ret op args ann body) = do
    body' <- simplifyStatements Nothing body
    return $ ProcedureDeclaration l ret op args ann body'

simplifyVariableDeclaration :: SimplifyK loc m => VariableDeclaration VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyVariableDeclaration (VariableDeclaration l t vs) = do
    (xs,t') <- simplifyTypeSpecifier t
    xs' <- concatMapM (simplifyVariableInitialization t') $ Foldable.toList vs
    return $ xs ++ xs'  
    
simplifyVariableInitialization :: SimplifyK loc m => TypeSpecifier VarIdentifier (Typed loc) -> VariableInitialization VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyVariableInitialization t (VariableInitialization l v szs mbe) = do
    (ss,szs') <- simplifyMaybeSizes szs
    let def = VariableDeclaration l t $ WrapNe $ VariableInitialization l v szs' Nothing
    ass <- case mbe of
        Nothing -> return []
        Just e -> do
            (ss',e') <- simplifyExpression e
            let ass' = maybe [] (\e -> [ExpressionStatement l $ BinaryAssign l (varExpr v) (BinaryAssignEqual noloc) e]) e'
            return (ss'++ass')
    return (ss ++ VarStatement l def:ass)

simplifyConstDeclaration :: SimplifyK loc m => ConstDeclaration VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyConstDeclaration (ConstDeclaration l t vs) = do
    (xs,t') <- simplifyTypeSpecifier t
    xs' <- concatMapM (simplifyConstInitialization t) $ Foldable.toList vs
    return $ xs ++ xs'  
    
simplifyConstInitialization :: SimplifyK loc m => TypeSpecifier VarIdentifier (Typed loc) -> ConstInitialization VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyConstInitialization t (ConstInitialization l v szs mbe) = do
    (ss,szs') <- simplifyMaybeSizes szs
    let def = ConstDeclaration l t $ WrapNe $ ConstInitialization l v szs' Nothing
    ass <- case mbe of
        Nothing -> return []
        Just e -> do
            (ss',e') <- simplifyExpression e
            let ass' = maybe [] (\e -> [ExpressionStatement l $ BinaryAssign l (varExpr v) (BinaryAssignEqual noloc) e]) e'
            return (ss'++ass')
    return (ss ++ ConstStatement l def:ass)

simplifyTypeSpecifier :: SimplifyT loc m TypeSpecifier
simplifyTypeSpecifier (TypeSpecifier l s t d) = do
    (ss,t') <- simplifyDatatypeSpecifier t
    (ss',d') <- simplifyMaybe simplifyDimtypeSpecifier d
    return (ss++ss',TypeSpecifier l s t' d')

simplifyDimtypeSpecifier :: SimplifyT loc m DimtypeSpecifier
simplifyDimtypeSpecifier (DimSpecifier l e) = do
    (ss,Just e') <- simplifyExpression e
    return (ss,DimSpecifier l e')

simplifyDatatypeSpecifier :: SimplifyT loc m DatatypeSpecifier
simplifyDatatypeSpecifier t@(PrimitiveSpecifier {}) = return ([],t)
simplifyDatatypeSpecifier t@(VariableSpecifier {}) = return ([],t)
simplifyDatatypeSpecifier (TemplateSpecifier l n args) = do
    (ss,args') <- simplifyList (simplifyVariadic simplifyTemplateTypeArgument) args
    return (ss,TemplateSpecifier l n args')

simplifyTemplateTypeArgument :: SimplifyT loc m TemplateTypeArgument
simplifyTemplateTypeArgument a@(GenericTemplateTypeArgument l arg) = return ([],a)
simplifyTemplateTypeArgument a@(TemplateTemplateTypeArgument l n args) = return ([],a)
simplifyTemplateTypeArgument a@(PrimitiveTemplateTypeArgument {}) = return ([],a)
simplifyTemplateTypeArgument (ExprTemplateTypeArgument l e) = do
    (ss,Just e') <- simplifyExpression e
    return (ss,ExprTemplateTypeArgument l e')
simplifyTemplateTypeArgument a@(PublicTemplateTypeArgument {}) = return ([],a)

simplifyMaybeSizes :: SimplifyM loc m (Maybe (Sizes VarIdentifier (Typed loc)))
simplifyMaybeSizes Nothing = return ([],Nothing)
simplifyMaybeSizes (Just (Sizes es)) = do
    (ss,es') <- simplifyVariadicExpressions $ Foldable.toList es
    if null es'
        then return (ss,Nothing)
        else return (ss,Just $ Sizes $ fromListNe es')

-- the splitted statements and expression must be pure
simplifyExpression :: SimplifyK loc m => Expression VarIdentifier (Typed loc) -> TcM m ([Statement VarIdentifier (Typed loc)],Maybe (Expression VarIdentifier (Typed loc)))
simplifyExpression (ProcCallExpr l n ts es) = do
    (ss,ts') <- simplifyMaybe (simplifyList (simplifyVariadic simplifyTemplateTypeArgument)) ts
    (ss',es') <- simplifyVariadicExpressions es
    mb <- inlineProcCall (unTyped l) (Left $ procedureNameId n) (typed $ loc n) es'
    case mb of
        Nothing -> return (ss++ss',Just $ ProcCallExpr l n ts' es')
        Just (ss'',res) -> return (ss++ss'++ss'',res)
simplifyExpression e@(BinaryExpr l e1 o e2) = do
    (ss1,Just e1') <- simplifyExpression e1
    (ss2,Just e2') <- simplifyExpression e2
    mb <- inlineProcCall (unTyped l) (Right $ fmap typed o) (typed $ loc o) [(e1',False),(e2',False)]
    case mb of
        Nothing -> return (ss1++ss2,Just $ BinaryExpr l e1' o e2')
        Just (ss3,res) -> return (ss1++ss2++ss3,res)
simplifyExpression (UnaryExpr l o e) = do
    (ss,Just e') <- simplifyExpression e
    mb <- inlineProcCall (unTyped l) (Right $ fmap typed o) (typed $ loc o) [(e',False)]
    case mb of
        Nothing -> return (ss,Just $ UnaryExpr l o e')
        Just (ss',res) -> return (ss++ss',res)
simplifyExpression (CondExpr l c e1 e2) = do
    (ssc,Just c') <- simplifyExpression c
    (ss1,Just e1') <- simplifyExpression e1
    (ss2,Just e2') <- simplifyExpression e2
    return (ssc++ss1++ss2,Just $ CondExpr l c' e1' e2')
simplifyExpression (BinaryAssign l e1 bop e2) = do
    let mb_op = binAssignOpToOp bop
    (ss,Just e2') <- case mb_op of
        Just op -> simplifyExpression (BinaryExpr l e1 op e2)
        Nothing -> simplifyExpression e2
    return (ss,Just $ BinaryAssign l e1 (BinaryAssignEqual l) e2')
simplifyExpression (PostIndexExpr l e s) = do
    (ss1,Just e') <- simplifyExpression e
    (ss2,s') <- simplifySubscript s
    return (ss1++ss2,Just $ PostIndexExpr l e' s')
simplifyExpression e = return ([],Just e)

simplifySubscript :: SimplifyT loc m Subscript
simplifySubscript s = return ([],s)

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

bindProcArgs :: SimplifyK loc m => loc -> [(Bool,Constrained Var,IsVariadic)] -> [Expression VarIdentifier (Typed loc)] -> TcM m ([Statement VarIdentifier (Typed loc)],Map VarIdentifier (Expression VarIdentifier (Typed loc)))
bindProcArgs l [] [] = return ([],Map.empty)
bindProcArgs l (v:vs) es = do
    (es',ss,substs) <- bindProcArg l v es
    (ss',substs') <- bindProcArgs l vs es'
    return (ss++ss',Map.union substs substs')

bindProcArg :: SimplifyK loc m => loc -> (Bool,Constrained Var,IsVariadic) -> [Expression VarIdentifier (Typed loc)] -> TcM m ([Expression VarIdentifier (Typed loc)],[Statement VarIdentifier (Typed loc)],Map VarIdentifier (Expression VarIdentifier (Typed loc)))
bindProcArg l (False,Constrained v _,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier t
    let tl = notTyped "bind" l
    let def = VarStatement tl $ VariableDeclaration tl t' $ WrapNe $ VariableInitialization tl (fmap (Typed l) v) Nothing $ Just e
    return (es,ss1++[def],Map.empty)
bindProcArg l (True,Constrained v _,False) (e:es) = do
    (t) <- type2TypeSpecifierNonVoid l (loc v)
    (ss1,t') <- simplifyTypeSpecifier t
    let tl = notTyped "bind" l
    let def = ConstStatement tl $ ConstDeclaration tl t' $ WrapNe $ ConstInitialization tl (fmap (Typed l) v) Nothing $ Just e
    return (es,ss1++[def],Map.empty)
bindProcArg l (_,Constrained v _,True) es = do
    sz <- evaluateIndexExpr (locpos l) =<< typeSize (locpos l) (loc v)
    let (es1,es2) = splitAt (fromEnum sz) es
    return (es2,[],Map.singleton (varNameId v) $ ArrayConstructorPExpr (Typed l $ loc v) es1)

splitProcAnns :: [ProcedureAnnotation iden loc] -> ([Statement iden loc],[Statement iden loc])
splitProcAnns [] = ([],[])
splitProcAnns (RequiresAnn p e:xs) = let (l,r) = splitProcAnns xs in (AnnStatement p [AssertAnn p e]:l,r)
splitProcAnns (EnsuresAnn p e:xs) = let (l,r) = splitProcAnns xs in (l,AnnStatement p [AssertAnn p e]:r)

-- inlines a procedures
-- we assume that typechecking has already tied the procedure's type arguments
inlineProcCall :: SimplifyK loc m => loc -> PIdentifier -> Type -> [(Expression VarIdentifier (Typed loc),IsVariadic)] -> TcM m (Maybe ([Statement VarIdentifier (Typed loc)],Maybe (Expression VarIdentifier (Typed loc))))
inlineProcCall l n t@(DecT d@(DecType _ _ _ _ _ _ _ _ (ProcType _ _ args ret ann body c))) es | isNonRecursiveDecType d = do
--    liftIO $ putStrLn $ "inline " ++ ppr es ++ " " ++ ppr t
    es' <- concatMapM unfoldVariadicExpr es
    (decls,substs) <- bindProcArgs l args es'
    ann' <- subst "inlineProcCall" (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) ann
    body' <- subst "inlineProcCall" (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos l))) body
    (mb) <- type2TypeSpecifier l ret
    let (reqs,ens) = splitProcAnns ann'
    case mb of
        Just t -> do
            (ss1,t') <- simplifyTypeSpecifier t
            res <- liftM (VarName (Typed l ret)) $ genVar (mkVarId "res")
            let tl = notTyped "inline" l
            let def = VarStatement tl $ VariableDeclaration tl t' $ WrapNe $ VariableInitialization tl res Nothing Nothing
            reqs' <- simplifyStatements Nothing reqs
            ss <- simplifyStatements (Just res) body'
            ens' <- simplifyStatements Nothing ens
            return $ Just (decls++ss1++[def,compoundStmt l (reqs'++ss++ens')],Just $ varExpr res)
        Nothing -> do
            reqs' <- simplifyStatements Nothing reqs
            ss <- simplifyStatements Nothing body'
            ens' <- simplifyStatements Nothing ens
            return $ Just ([compoundStmt l (decls++reqs'++ss++ens')],Nothing)
inlineProcCall l n t es = do
--    liftIO $ putStrLn $ "not inline " ++ ppr n ++ " " ++ ppr es ++ " " ++ ppr t
    return Nothing

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
    (ss,Just c') <- simplifyExpression c
    s1' <- simplifyStatement ret s1
    s2' <- simplifyStatements ret $ maybeToList s2
    return $ (ss++[IfStatement l c' (compoundStmt (unTyped l) s1') (if null s2 then Nothing else Just (compoundStmt (unTyped l) s2'))])
simplifyStatement Nothing (ReturnStatement l Nothing) = return []
simplifyStatement Nothing (ReturnStatement l (Just e)) = return [ReturnStatement l (Just e)]
simplifyStatement ret (ReturnStatement l (Just e)) = do
    (ss,e') <- simplifyExpression e
    case (ret,e') of
        (Just v,Just e') -> return (ss++[ExpressionStatement l $ BinaryAssign (loc v) (varExpr v) (BinaryAssignEqual l) e'])
        (Nothing,Nothing) -> return ss
        otherwise -> genError (locpos $ unTyped l) $ text "simplifyStatement: mismamtching return type"
simplifyStatement ret (ReturnStatement l e) = genError (locpos $ unTyped l) $ text "simplifyStatement: return statement"
simplifyStatement ret (AssertStatement l e) = do
    (ss,e') <- simplifyExpression e
    let s' = maybe [] (\e -> [AssertStatement l e]) e'
    return (ss++s')
simplifyStatement ret (ExpressionStatement l e) = do
    (ss,e') <- simplifyExpression e
    let s' = maybe [] (\e -> [ExpressionStatement l e]) e'
    return (ss++s')
simplifyStatement ret (VarStatement l v) = do
    simplifyVariableDeclaration v
simplifyStatement ret (ConstStatement l v) = do
    simplifyConstDeclaration v
simplifyStatement ret (WhileStatement l c ann s) = do
    s' <- simplifyStatement ret s
    return [WhileStatement l c ann $ compoundStmt (unTyped l) s']
simplifyStatement ret (ForStatement l e c i ann s) = do
    ss <- simplifyForInitializer e
    s' <- simplifyStatement ret s
    return (ss++[ForStatement l (InitializerExpression Nothing) c i ann $ compoundStmt (unTyped l) s'])
simplifyStatement ret (DowhileStatement l ann s c) = do
    s' <- simplifyStatement ret s
    (ss,Just c') <- simplifyExpression c
    return [DowhileStatement l ann (compoundStmt (unTyped l) $ s'++ss) c']
simplifyStatement ret (PrintStatement l es) = do
    (ss,es') <- simplifyVariadicExpressions es
    return (ss++[PrintStatement l es'])
simplifyStatement ret s = return [s]

--    | SyscallStatement loc String [SyscallParameter iden loc]

simplifyForInitializer :: SimplifyK loc m => ForInitializer VarIdentifier (Typed loc) -> TcM m [Statement VarIdentifier (Typed loc)]
simplifyForInitializer i@(InitializerExpression Nothing) = return []
simplifyForInitializer (InitializerExpression (Just e)) = do
    (ss,e') <- simplifyExpression e
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

simplifyVariadicExpressions :: SimplifyM loc m [(Expression VarIdentifier (Typed loc),IsVariadic)]
simplifyVariadicExpressions es = do
    (ss,es') <- mapAndUnzipM simplifyVariadicExpression es
    return (concat ss,concat es')

simplifyVariadicExpression :: SimplifyK loc m => (Expression VarIdentifier (Typed loc),IsVariadic) -> TcM m ([Statement VarIdentifier (Typed loc)],[(Expression VarIdentifier (Typed loc),IsVariadic)])
simplifyVariadicExpression (e,isVariadic) = do
    (ss,Just e') <- simplifyExpression e
    case (e',isVariadic) of
        (ArrayConstructorPExpr l es,True) -> return (ss,map (,False) es)
        p -> return (ss,[p])
        
simplifyMaybe :: SimplifyM loc m a -> SimplifyM loc m (Maybe a) 
simplifyMaybe m Nothing = return ([],Nothing)
simplifyMaybe m (Just x) = do
    (ss,x') <- m x
    return (ss,Just x')

simplifySizes :: SimplifyM loc m (Maybe (Sizes VarIdentifier (Typed loc)))
simplifySizes = simplifyMaybe $ \(Sizes xs) -> do
    (ss,xs') <- simplifyVariadicExpressions (Foldable.toList xs)
    return (ss,Sizes $ fromListNe xs')


