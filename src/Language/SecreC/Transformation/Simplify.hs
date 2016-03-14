{-# LANGUAGE TupleSections, ConstraintKinds, ViewPatterns, FlexibleContexts, RankNTypes #-}

module Language.SecreC.Transformation.Simplify where

import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Conversion
import Language.SecreC.TypeChecker.Semantics
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Expression
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Error
import Language.SecreC.Position
import Language.SecreC.Monad

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

type SimplifyK loc m = (MonadReader Options m,MonadBaseControl IO m,Typeable m,MonadIO m,Location loc,Vars VarIdentifier m loc,MonadError SecrecError m)

type SimplifyM loc m a = SimplifyK loc m => a -> m ([Statement VarIdentifier (Typed loc)],a)
type SimplifyT loc m a = SimplifyM loc m (a VarIdentifier (Typed loc))

type SimplifyG loc m a = SimplifyK loc m => a VarIdentifier (Typed loc) -> m (a VarIdentifier (Typed loc))

simplifyModuleWithPPArgs :: SimplifyK loc m => (PPArgs,Module VarIdentifier (Typed loc)) -> m (PPArgs,Module VarIdentifier (Typed loc))
simplifyModuleWithPPArgs (ppargs,x) = local (`mappend` ppOptions ppargs) (liftM (ppargs,) $ simplifyModule x)

simplifyModule :: SimplifyG loc m Module
simplifyModule m@(Module l n p) = do
    opts <- Reader.ask
    if (simplify opts)
        then do
            when (debugTransformation opts) $
                liftIO $ hPutStrLn stderr ("Simplifying module " ++ ppr (moduleVarId m) ++ "...")
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
simplifyProcedureDeclaration (OperatorDeclaration l ret op args body) = do
    body' <- simplifyStatements Nothing body
    return $ OperatorDeclaration l ret op args body'
simplifyProcedureDeclaration (ProcedureDeclaration l ret op args body) = do
    body' <- simplifyStatements Nothing body
    return $ ProcedureDeclaration l ret op args body'

simplifyVariableDeclaration :: SimplifyK loc m => VariableDeclaration VarIdentifier (Typed loc) -> m [Statement VarIdentifier (Typed loc)]
simplifyVariableDeclaration (VariableDeclaration l t vs) = do
    (xs,t') <- simplifyTypeSpecifier t
    xs' <- concatMapM (simplifyVariableInitialization t') $ Foldable.toList vs
    return $ xs ++ xs'  
    
simplifyVariableInitialization :: SimplifyK loc m => TypeSpecifier VarIdentifier (Typed loc) -> VariableInitialization VarIdentifier (Typed loc) -> m [Statement VarIdentifier (Typed loc)]
simplifyVariableInitialization t (VariableInitialization l v szs mbe) = do
    (ss,szs') <- simplifyMaybeSizes szs
    let def = VariableDeclaration l t $ WrapNe $ VariableInitialization l v szs' Nothing
    ass <- case mbe of
        Nothing -> return []
        Just e -> do
            (ss',e') <- simplifyExpression e
            let ass' = BinaryAssign l (varExpr v) (BinaryAssignEqual noloc) e'
            return (ss'++[ExpressionStatement l ass'])
    return (ss ++ VarStatement l def:ass)

simplifyConstDeclaration :: SimplifyK loc m => ConstDeclaration VarIdentifier (Typed loc) -> m [Statement VarIdentifier (Typed loc)]
simplifyConstDeclaration (ConstDeclaration l t vs) = do
    (xs,t') <- simplifyTypeSpecifier t
    xs' <- concatMapM (simplifyConstInitialization t) $ Foldable.toList vs
    return $ xs ++ xs'  
    
simplifyConstInitialization :: SimplifyK loc m => TypeSpecifier VarIdentifier (Typed loc) -> ConstInitialization VarIdentifier (Typed loc) -> m [Statement VarIdentifier (Typed loc)]
simplifyConstInitialization t (ConstInitialization l v szs mbe) = do
    (ss,szs') <- simplifyMaybeSizes szs
    let def = ConstDeclaration l t $ WrapNe $ ConstInitialization l v szs' Nothing
    ass <- case mbe of
        Nothing -> return []
        Just e -> do
            (ss',e') <- simplifyExpression e
            let ass' = BinaryAssign l (varExpr v) (BinaryAssignEqual noloc) e'
            return (ss'++[ExpressionStatement l ass'])
    return (ss ++ ConstStatement l def:ass)

simplifyTypeSpecifier :: SimplifyT loc m TypeSpecifier
simplifyTypeSpecifier (TypeSpecifier l s t d) = do
    (ss,t') <- simplifyDatatypeSpecifier t
    (ss',d') <- simplifyMaybe simplifyDimtypeSpecifier d
    return (ss++ss',TypeSpecifier l s t' d')

simplifyDimtypeSpecifier :: SimplifyT loc m DimtypeSpecifier
simplifyDimtypeSpecifier (DimSpecifier l e) = do
    (ss,e') <- simplifyExpression e
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
    (ss,e') <- simplifyExpression e
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
simplifyExpression :: SimplifyT loc m Expression
simplifyExpression (ProcCallExpr l n ts es) = do
    (ss,ts') <- simplifyMaybe (simplifyList (simplifyVariadic simplifyTemplateTypeArgument)) ts
    (ss',es') <- simplifyVariadicExpressions es
    mb <- inlineProcCall (typed $ loc n) es'
    case mb of
        Nothing -> return (ss++ss',ProcCallExpr l n ts' es')
        Just (ss'',res) -> case res of
            Nothing -> genError noloc $ text "simplifyExpression: procedure with void return type"
            Just r -> return (ss++ss'++ss'',r)
simplifyExpression e@(BinaryExpr l e1 o e2) = do
    (ss1,e1') <- simplifyExpression e1
    (ss2,e2') <- simplifyExpression e2
    mb <- inlineProcCall (typed $ loc o) [(e1',False),(e2',False)]
    case mb of
        Nothing -> return (ss1++ss2,BinaryExpr l e1' o e2')
        Just (ss3,res) -> case res of
            Nothing -> genError noloc $ text "simplifyExpression: procedure with void return type"
            Just r -> return (ss1++ss2++ss3,r)
simplifyExpression (UnaryExpr l o e) = do
    (ss,e') <- simplifyExpression e
    mb <- inlineProcCall (typed $ loc o) [(e',False)]
    case mb of
        Nothing -> return (ss,UnaryExpr l o e')
        Just (ss',res) -> case res of
            Nothing -> genError noloc $ text "simplifyExpression: procedure with void return type"
            Just r -> return (ss++ss',r)
simplifyExpression (CondExpr l c e1 e2) = do
    (ssc,c') <- simplifyExpression c
    (ss1,e1') <- simplifyExpression e1
    (ss2,e2') <- simplifyExpression e2
    return (ssc++ss1++ss2,CondExpr l c' e1' e2')
simplifyExpression (BinaryAssign l e1 bop e2) = do
    let mb_op = binAssignOpToOp bop
    (ss,e2') <- case mb_op of
        Just op -> simplifyExpression (BinaryExpr l e1 op e2)
        Nothing -> simplifyExpression e2
    return (ss,BinaryAssign l e1 (BinaryAssignEqual noloc) e2')
simplifyExpression (PostIndexExpr l e s) = do
    (ss1,e') <- simplifyExpression e
    (ss2,s') <- simplifySubscript s
    return (ss1++ss2,PostIndexExpr l e' s')
simplifyExpression e = return ([],e)

simplifySubscript :: SimplifyT loc m Subscript
simplifySubscript s = return ([],s)

--simplifyExpression (QualExpr l e t) = do
--    | DomainIdExpr loc (SecTypeSpecifier VarIdentifier loc)
--    | BytesFromStringExpr loc (Expression VarIdentifier loc)
--    | StringFromBytesExpr loc (Expression VarIdentifier loc)
--    | VArraySizeExpr loc (Expression VarIdentifier loc)
--    | SelectionExpr loc (Expression VarIdentifier loc) (AttributeName VarIdentifier loc)

unfoldVariadicExpr :: SimplifyK loc m => (Expression VarIdentifier loc,IsVariadic) -> m [Expression VarIdentifier loc]
unfoldVariadicExpr (e,False) = return [e]
unfoldVariadicExpr (ArrayConstructorPExpr _ es,True) = return es
unfoldVariadicExpr ve = genError noloc $ text "unfoldVariadicExpr"

bindProcArgs :: SimplifyK loc m => [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)] -> [Expression VarIdentifier (Typed loc)] -> m ([Statement VarIdentifier (Typed loc)],Map VarIdentifier (Expression VarIdentifier (Typed loc)))
bindProcArgs [] [] = return ([],Map.empty)
bindProcArgs (v:vs) es = do
    (es',ss,substs) <- bindProcArg v es
    (ss',substs') <- bindProcArgs vs es'
    return (ss++ss',Map.union substs substs')

bindProcArg :: SimplifyK loc m => (Bool,Cond (VarName VarIdentifier Type),IsVariadic) -> [Expression VarIdentifier (Typed loc)] -> m ([Expression VarIdentifier (Typed loc)],[Statement VarIdentifier (Typed loc)],Map VarIdentifier (Expression VarIdentifier (Typed loc)))
bindProcArg (False,Cond v _,False) (e:es) = do
    (t,szs) <- type2SizedTypeSpecifierNonVoid (loc v)
    (ss1,t') <- simplifyTypeSpecifier t
    (ss2,szs') <- simplifyMaybeSizes szs
    let def = VarStatement noloc $ VariableDeclaration noloc t' $ WrapNe $ VariableInitialization noloc (fmap (Typed noloc) v) szs' $ Just e
    return (es,ss1++ss2++[def],Map.empty)
bindProcArg (True,Cond v _,False) (e:es) = do
    (t,szs) <- type2SizedTypeSpecifierNonVoid (loc v)
    (ss1,t') <- simplifyTypeSpecifier t
    (ss2,szs') <- simplifyMaybeSizes szs
    let def = ConstStatement noloc $ ConstDeclaration noloc t' $ WrapNe $ ConstInitialization noloc (fmap (Typed noloc) v) szs' $ Just e
    return (es,ss1++ss2++[def],Map.empty)
bindProcArg (_,Cond v _,True) es = do
    sz <- runSecrecM mempty $ runTcM $ evaluateTypeSize (noloc::Position) (loc v)
    let (es1,es2) = splitAt (fromEnum sz) es
    return (es2,[],Map.singleton (varNameId v) $ ArrayConstructorPExpr (Typed noloc $ loc v) es1)

-- inlines a procedures
-- we assume that typechecking has already tied the procedure's type arguments
inlineProcCall :: SimplifyK loc m => Type -> [(Expression VarIdentifier (Typed loc),IsVariadic)] -> m (Maybe ([Statement VarIdentifier (Typed loc)],Maybe (Expression VarIdentifier (Typed loc))))
inlineProcCall t@(DecT d@(DecType _ _ _ _ _ _ _ _ (ProcType _ _ args ret body c))) es | isNonRecursiveDecType d = do
--    liftIO $ putStrLn $ "inline " ++ ppr es ++ " " ++ ppr t
    es' <- concatMapM unfoldVariadicExpr es
    (decls,substs) <- bindProcArgs args es'
    body' <- subst "inlineProcCall" (substsFromMap substs) False Map.empty $ map (fmap (fmap (updpos noloc))) body
    mb <- type2SizedTypeSpecifier ret
    case mb of
        Just (t,szs) -> do
            (ss1,t') <- simplifyTypeSpecifier t
            (ss2,szs') <- simplifyMaybeSizes szs
            res <- liftM (VarName (Typed noloc ret)) $ freshVarId "res" Nothing
            let def = VarStatement noloc $ VariableDeclaration noloc t' $ WrapNe $ VariableInitialization noloc res szs' Nothing
            ss <- simplifyStatements (Just res) body'
            return $ Just (decls++ss1++ss2++[def,compoundStmt ss],Just $ varExpr res)
        Nothing -> do
            ss <- simplifyStatements Nothing body'
            return $ Just ([compoundStmt (decls++ss)],Nothing)
inlineProcCall t es = do
--    liftIO $ putStrLn $ "not inline " ++ ppr es ++ " " ++ ppr t
    return Nothing

simplifyStatements :: SimplifyK loc m => Maybe (VarName VarIdentifier (Typed loc)) -> [Statement VarIdentifier (Typed loc)] -> m [Statement VarIdentifier (Typed loc)]
simplifyStatements ret [] = return []
simplifyStatements ret (s:ss) = do
    ss1 <- simplifyStatement ret s
    ss2 <- simplifyStatements ret ss
    return (ss1++ss2)

simplifyStatement :: SimplifyK loc m => Maybe (VarName VarIdentifier (Typed loc)) -> Statement VarIdentifier (Typed loc) -> m [Statement VarIdentifier (Typed loc)]
simplifyStatement ret (CompoundStatement l ss) = do
    ss' <- simplifyStatements ret ss
    return [CompoundStatement l ss']
simplifyStatement ret (IfStatement l c s1 s2) = do
    (ss,c') <- simplifyExpression c
    s1' <- simplifyStatement ret s1
    s2' <- simplifyStatements ret $ maybeToList s2
    return $ (ss++[IfStatement l c' (compoundStmt s1') (if null s2 then Nothing else Just (compoundStmt s2'))])
simplifyStatement Nothing (ReturnStatement l Nothing) = return []
simplifyStatement Nothing (ReturnStatement l (Just e)) = return [ReturnStatement l (Just e)]
simplifyStatement (Just v) (ReturnStatement l (Just e)) = do
    (ss,e') <- simplifyExpression e
    return (ss++[ExpressionStatement l $ BinaryAssign (loc v) (varExpr v) (BinaryAssignEqual noloc) e'])
simplifyStatement ret (ReturnStatement l e) = genError noloc $ text "simplifyStatement: return statement"
simplifyStatement ret (AssertStatement l e) = do
    (ss,e') <- simplifyExpression e
    return (ss++[AssertStatement l e'])
simplifyStatement ret (ExpressionStatement l e) = do
    (ss,e') <- simplifyExpression e
    return (ss++[ExpressionStatement l e'])
simplifyStatement ret (VarStatement l v) = do
    simplifyVariableDeclaration v
simplifyStatement ret (ConstStatement l v) = do
    simplifyConstDeclaration v
simplifyStatement ret (WhileStatement l c s) = do
    s' <- simplifyStatement ret s
    return [WhileStatement l c $ compoundStmt s']
simplifyStatement ret (ForStatement l e c i s) = do
    ss <- simplifyForInitializer e
    s' <- simplifyStatement ret s
    return (ss++[ForStatement l (InitializerExpression Nothing) c i $ compoundStmt s'])
simplifyStatement ret (DowhileStatement l s c) = do
    s' <- simplifyStatement ret s
    (ss,c') <- simplifyExpression c
    return [DowhileStatement l (compoundStmt $ s'++ss) c']
simplifyStatement ret (PrintStatement l es) = do
    (ss,es') <- simplifyVariadicExpressions es
    return (ss++[PrintStatement l es'])
simplifyStatement ret s = return [s]

--    | SyscallStatement loc String [SyscallParameter iden loc]

simplifyForInitializer :: SimplifyK loc m => ForInitializer VarIdentifier (Typed loc) -> m [Statement VarIdentifier (Typed loc)]
simplifyForInitializer i@(InitializerExpression Nothing) = return []
simplifyForInitializer (InitializerExpression (Just e)) = do
    (ss,e') <- simplifyExpression e
    return (ss++[ExpressionStatement (loc e') e'])
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

simplifyVariadicExpression :: SimplifyK loc m => (Expression VarIdentifier (Typed loc),IsVariadic) -> m ([Statement VarIdentifier (Typed loc)],[(Expression VarIdentifier (Typed loc),IsVariadic)])
simplifyVariadicExpression (e,isVariadic) = do
    (ss,e') <- simplifyExpression e
    case (e',isVariadic) of
        (ArrayConstructorPExpr l es,True) -> return (ss,map (,False) es)
        p -> return (ss,[p])
        
simplifyMaybe :: SimplifyM loc m a -> SimplifyM loc m (Maybe a) 
simplifyMaybe m Nothing = return ([],Nothing)
simplifyMaybe m (Just x) = do
    (ss,x') <- m x
    return (ss,Just x')




