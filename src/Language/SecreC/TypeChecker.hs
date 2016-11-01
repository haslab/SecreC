{-# LANGUAGE ScopedTypeVariables, TupleSections, FlexibleContexts, ViewPatterns, DeriveDataTypeable #-}

-- We delay resolution of all possible constraints inside the  body of templates, even those that do not depend on template variables, to better match C++ templates that are only typechecked on full instantiation.

module Language.SecreC.TypeChecker where

import Language.SecreC.Monad
import Language.SecreC.Modules
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Statement
import Language.SecreC.TypeChecker.Expression
import Language.SecreC.TypeChecker.Type
import Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import Language.SecreC.TypeChecker.Conversion
import Language.SecreC.TypeChecker.Template
import Language.SecreC.Utils
import Language.SecreC.Vars
import Language.SecreC.Pretty
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Prover.Base
import Language.SecreC.Prover.Expression
import Language.SecreC.Transformation.Simplify

import Prelude hiding (mapM)
import Safe

import Data.Maybe
import Data.UnixTime
import Data.Bifunctor
import Data.Binary
import Data.Generics
import Data.Traversable
import Data.Foldable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Graph.Inductive.Graph as Graph

import Control.Monad hiding (mapM,mapAndUnzipM)
import Control.Monad.IO.Class
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import qualified Control.Monad.Reader as Reader
import Control.Monad.Trans

import System.IO
import System.Posix.Time
import System.Posix.Files
import System.FilePath.Posix

import Text.PrettyPrint as PP hiding (float,int,equals)
import qualified Text.PrettyPrint as Pretty hiding (equals)

tcModuleFile :: ProverK Position m => ModuleFile -> TcM m TypedModuleFile
tcModuleFile (Left (t,args,m)) = do
    (args',m') <- tcModuleWithPPArgs (args,m)
    return $ Left (t,args',m')
tcModuleFile (Right sci) = do
    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (mappend x y,sciEnv sci) }
    return $ Right sci

tcModuleWithPPArgs :: (ProverK loc m) => (PPArgs,Module Identifier loc) -> TcM m (PPArgs,Module GIdentifier (Typed loc))
tcModuleWithPPArgs (ppargs,x) = localOptsTcM (`mappend` ppOptions ppargs) $ do
    --debugTc $ liftIO $ putStrLn $ "typechecking args ..." ++ show ppargs
    x' <- tcModule x
    menv <- State.gets (snd . moduleEnv)
    TcM $ lift $ writeModuleSCI ppargs menv x
    return (ppargs,x')

tcModule :: (ProverK loc m) => Module Identifier loc -> TcM m (Module GIdentifier (Typed loc))
tcModule m@(Module l name prog) = failTcM l $ do
    opts' <- TcM $ State.lift Reader.ask
    --debugTc $ liftIO $ putStrLn $ "typechecking ..." ++ show opts'
    when (debugTypechecker opts') $ do
        ppm <- ppr (moduleId $ fmap locpos m)
        liftIO $ hPutStrLn stderr ("Typechecking module " ++ ppm ++ "...")
    -- reset module typechecking environment and increment module count
    State.modify $ \env -> env
        { moduleCount = (Just (moduleId m,TyVarId 0),succ $ snd $ moduleCount env)
        , moduleEnv = let (x,y) = moduleEnv env in (x `mappend` y,mempty)
        }
    liftIO resetTyVarId
    -- typecheck the program
    prog' <- tcProgram prog
    -- substitute the module's environment with the module's dictionary
    --ss <- getTSubsts
    --modifyModuleEnvM $ substFromTSubsts "tcModule" l ss False Map.empty
    --State.modify $ \env -> env { tDict = [] }
    let m' = Module (notTyped "tcModule" l) (fmap (bimap (MIden . mkVarId) (notTyped "tcModule")) name) prog'
    --m'' <- substFromTSubsts "tcModule" l ss False Map.empty m'
    return m'

tcProgram :: (ProverK loc m) => Program Identifier loc -> TcM m (Program GIdentifier (Typed loc))
tcProgram (Program l imports globals) = do
    let imports' = map (bimap (MIden . mkVarId) (notTyped "tcProgram")) imports
    globals' <- mapM tcGlobalDeclaration globals
    return $ Program (notTyped "tcProgram" l) imports' globals'

tcGlobalDeclaration :: (ProverK loc m) => GlobalDeclaration Identifier loc -> TcM m (GlobalDeclaration GIdentifier (Typed loc))
tcGlobalDeclaration (GlobalVariable l vd) = tcGlobal l $ do
    vd' <- tcVarDecl GlobalScope vd
    return $ GlobalVariable (notTyped "tcGlobalDeclaration" l) vd'
tcGlobalDeclaration (GlobalDomain l dd) = tcGlobal l $ do
    dd' <- tcDomainDecl dd
    return $ GlobalDomain (notTyped "tcGlobalDeclaration" l) dd'
tcGlobalDeclaration (GlobalKind l kd) = tcGlobal l $ do
    kd' <- tcKindDecl kd
    return $ GlobalKind (notTyped "tcGlobalDeclaration" l) kd'
tcGlobalDeclaration (GlobalProcedure l pd) = tcGlobal l $ do
    (pd') <- tcProcedureDecl (const newOperator) (const newProcedureFunction) pd
    return $ GlobalProcedure (notTyped "tcGlobalDeclaration" l) pd'
tcGlobalDeclaration (GlobalFunction l pd) = tcGlobal l $ do
    (pd') <- tcFunctionDecl (const newOperator) (const newProcedureFunction) pd
    return $ GlobalFunction (notTyped "tcGlobalDeclaration" l) pd'
tcGlobalDeclaration (GlobalStructure l sd) = tcGlobal l $ do
    (sd') <- tcStructureDecl (const newStruct) sd
    return $ GlobalStructure (notTyped "tcGlobalDeclaration" l) sd'
tcGlobalDeclaration (GlobalTemplate l td) = tcGlobal l $ do
    td' <- tcTemplateDecl td
    let res = GlobalTemplate (notTyped "tcGlobalDeclaration" l) td'
    return res
tcGlobalDeclaration (GlobalAnnotations l ann) = do
    ann' <- mapM tcGlobalAnn ann
    return $ GlobalAnnotations (notTyped "tcGlobalAnnotation" l) ann'

tcGlobalAnn :: ProverK loc m => GlobalAnnotation Identifier loc -> TcM m (GlobalAnnotation GIdentifier (Typed loc))
tcGlobalAnn (GlobalFunctionAnn l proc) = tcGlobal l $ insideAnnotation $ do
    (proc') <- tcFunctionDecl (const newOperator) (const newProcedureFunction) proc
    return $ GlobalFunctionAnn (notTyped "tcGlobalAnn" l) proc'
tcGlobalAnn (GlobalProcedureAnn l proc) = tcGlobal l $ insideAnnotation $ do
    (proc') <- tcProcedureDecl (const newOperator) (const newProcedureFunction) proc
    return $ GlobalProcedureAnn (notTyped "tcGlobalAnn" l) proc'
tcGlobalAnn (GlobalStructureAnn l proc) = tcGlobal l $ insideAnnotation $ do
    (proc') <- tcStructureDecl (const newStruct) proc
    return $ GlobalStructureAnn (notTyped "tcGlobalAnn" l) proc'
tcGlobalAnn (GlobalTemplateAnn l proc) = tcGlobal l $ insideAnnotation $ do
    proc' <- tcTemplateDecl proc
    return $ GlobalTemplateAnn (notTyped "tcGlobalAnn" l) proc'
tcGlobalAnn (GlobalAxiomAnn l ax) = tcGlobal l $ insideAnnotation $ do
    ax' <- tcAxiomDecl ax
    return $ GlobalAxiomAnn (notTyped "tcGlobalAnn" l) ax'
tcGlobalAnn (GlobalLemmaAnn l ax) = tcGlobal l $ insideAnnotation $ do
    ax' <- tcLemmaDecl ax
    return $ GlobalLemmaAnn (notTyped "tcGlobalAnn" l) ax'

tcDomainDecl :: ProverK loc m => DomainDeclaration Identifier loc -> TcM m (DomainDeclaration GIdentifier (Typed loc))
tcDomainDecl (Domain l (DomainName dl dn) k) = do
    let vk@(KindName _ kn) = bimap (mkVarId) id k
    let t = KindT $ PrivateK $ TIden kn
    let d' = DomainName (Typed dl t) $ TIden $ mkVarId dn
    newDomain d'
    isAnn <- getAnn
    checkKind isAnn vk
    return $ Domain (notTyped "tcDomainDecl" l) d' (bimap (TIden . mkVarId) (notTyped "tcDomainDecl") k)

tcKindDecl :: ProverK loc m => KindDeclaration Identifier loc -> TcM m (KindDeclaration GIdentifier (Typed loc))
tcKindDecl (Kind l k) = do
    k' <- tcKindName k
    newKind k'
    return $ Kind (Typed l $ KType $ Just NonPublicClass) k'
    
tcKindName :: ProverK loc m => KindName Identifier loc -> TcM m (KindName GIdentifier (Typed loc))
tcKindName (KindName kl kn) = return $ KindName (Typed kl (KType $ Just NonPublicClass)) $ TIden $ mkVarId kn

tcAxiomDecl :: ProverK loc m => AxiomDeclaration Identifier loc -> TcM m (AxiomDeclaration GIdentifier (Typed loc))
tcAxiomDecl (AxiomDeclaration l isLeak qs ps ann) = withKind AKind $ defaultInline $ withLeak isLeak $ do
    (tvars',vars') <- tcAddDeps l "tcAxiomDecl" $ do
        (qs',tvars') <- mapAndUnzipM tcTemplateQuantifier qs
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        return (tvars',vars')
    hdeps <- getDeps
    ann' <- tcProcedureAnns ann
    cl <- getDecClass
    let idec = AxiomType isLeak (locpos l) vars' (map (fmap (fmap locpos)) ann') cl
    dec <- newAxiom l tvars' hdeps idec
    dec2AxiomDecl l dec

tcLemmaDecl :: ProverK loc m => LemmaDeclaration Identifier loc -> TcM m (LemmaDeclaration GIdentifier (Typed loc))
tcLemmaDecl (LemmaDeclaration l isLeak n@(ProcedureName pl pn) qs hctx ps bctx@(TemplateContext _ mb) ann body) = withInCtx (isJust mb) $ tcTemplate l $ withKind LKind $ defaultInline $ withLeak isLeak $ do
    (tvars',hctx',vars',bctx') <- tcAddDeps l "tcAxiomDecl" $ do
        (qs',tvars') <- mapAndUnzipM tcTemplateQuantifier qs
        hctx' <- tcTemplateContext hctx
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        bctx' <- tcTemplateContext bctx
        return (tvars',hctx',vars',bctx')
    hdeps <- getDeps
    ann' <- tcProcedureAnns ann
    let tret = ComplexT Void
    s' <- mapM (tcStmtsRet l tret) body
    cl <- getDecClass
    let idec = IDecT $ LemmaType isLeak (locpos l) (PIden $ mkVarId pn) vars' (map (fmap (fmap locpos)) ann') (fmap (map (fmap (fmap locpos))) s') cl
    let lemma' = ProcedureName (Typed pl idec) $ PIden $ mkVarId pn
    let hdecctx = (\(DecCtxT x) -> x) $ typed $ loc hctx'
    let bdecctx = (\(DecCtxT x) -> x) $ typed $ loc bctx'
    lemma'' <- newLemma tvars' hdecctx bdecctx hdeps lemma'
    dec2LemmaDecl l $ unDecT $ typed $ loc lemma''

tcFunctionDecl :: (ProverK loc m) => (DecCtx -> DecCtx -> Deps -> Op GIdentifier (Typed loc) -> TcM m (Op GIdentifier (Typed loc))) -> (DecCtx -> DecCtx -> Deps -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc)))
                -> FunctionDeclaration Identifier loc -> TcM m (FunctionDeclaration GIdentifier (Typed loc))
tcFunctionDecl addOp _ (OperatorFunDeclaration l isLeak ret op ps bctx@(TemplateContext _ mb) ann s) = withInCtx (isJust mb) $ withKind FKind $ defaultInline $ withLeak isLeak $ do
    (ps',ret',vars',bctx',top,tret,vret) <- tcAddDeps l "tcFunctionDecl" $ do
        top <- tcOp op
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        bctx' <- tcTemplateContext bctx
        ret' <- tcTypeSpec ret False True
        let tret = typed $ loc ret'
        when isLeak $ tcCstrM_ l $ Unifies tret (BaseT bool)
        vret <- do
            let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
            newVariable LocalScope True True vr Nothing
            return vr
        return (ps',ret',vars',bctx',top,tret,vret)
    hdeps <- getDeps
    ann' <- tcProcedureAnns ann
    s' <- tcExprTy tret s
    dropLocalVar vret
    cl <- getDecClass
    let tproc = IDecT $ FunType isLeak (locpos l) (OIden $ fmap typed top) vars' tret (map (fmap (fmap locpos)) ann') (Just $ fmap (fmap locpos) s') cl
    let op' = updLoc top (Typed l tproc)
    let bdecctx = (\(DecCtxT x) -> x) $ typed $ loc bctx'
    op'' <- addOp explicitDecCtx bdecctx hdeps op'
    dec2FunDecl l $ unDecT $ typed $ loc op''
tcFunctionDecl _ addProc (FunDeclaration l isLeak ret (ProcedureName pl pn) ps bctx@(TemplateContext _ mb) ann s) = withInCtx (isJust mb) $ withKind FKind $ defaultInline $ withLeak isLeak $ do
    (ps',ret',vars',bctx',tret,vret) <- tcAddDeps l "tcFunctionDecl" $ do
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        bctx' <- tcTemplateContext bctx
        ret' <- tcTypeSpec ret False True
        let tret = typed $ loc ret'
        when isLeak $ tcCstrM_ l $ Unifies tret (BaseT bool)
        vret <- do
            let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
            newVariable LocalScope True True vr Nothing
            return vr
        return (ps',ret',vars',bctx',tret,vret)
    hdeps <- getDeps
    ann' <- tcProcedureAnns ann
    s' <- tcExprTy tret s
    dropLocalVar vret
    cl <- getDecClass
    let tproc = IDecT $ FunType isLeak (locpos l) (PIden $ mkVarId pn) vars' tret (map (fmap (fmap locpos)) ann') (Just $ fmap (fmap locpos) s') cl
    let proc' = ProcedureName (Typed pl tproc) $ PIden $ mkVarId pn
    let bdecctx = (\(DecCtxT x) -> x) $ typed $ loc bctx'
    proc'' <- addProc explicitDecCtx bdecctx hdeps proc'
    dec2FunDecl l $ unDecT $ typed $ loc proc''

tcProcedureDecl :: (ProverK loc m) => (DecCtx -> DecCtx -> Deps -> Op GIdentifier (Typed loc) -> TcM m (Op GIdentifier (Typed loc))) -> (DecCtx -> DecCtx -> Deps -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc)))
                -> ProcedureDeclaration Identifier loc -> TcM m (ProcedureDeclaration GIdentifier (Typed loc))
tcProcedureDecl addOp _ (OperatorDeclaration l ret op ps bctx@(TemplateContext _ mb) ann s) = withInCtx (isJust mb) $ withKind PKind $ defaultInline $ do
    (ps',bctx',ret',vars',top,tret,vret) <- tcAddDeps l "tcProcedureDecl" $ do
        top <- tcOp op
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        bctx' <- tcTemplateContext bctx
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        vret <- case ret' of
            ReturnType _ Nothing -> return Nothing
            ReturnType _ (Just _) -> do
                let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
                newVariable LocalScope True True vr Nothing
                return $ Just vr
        return (ps',bctx',ret',vars',top,tret,vret)
    hdeps <- getDeps
    ann' <- tcProcedureAnns ann
    mapM_ dropLocalVar vret
    s' <- tcStmtsRet l tret s
    cl <- getDecClass
    let tproc = IDecT $ ProcType (locpos l) (OIden $ fmap typed top) vars' tret (map (fmap (fmap locpos)) ann') (Just $ map (fmap (fmap locpos)) s') cl
    let op' = updLoc top (Typed l tproc)
    let bdecctx = (\(DecCtxT x) -> x) $ typed $ loc bctx'
    op'' <- addOp explicitDecCtx bdecctx hdeps op'
    dec2ProcDecl l $ unDecT $ typed $ loc op''
tcProcedureDecl _ addProc (ProcedureDeclaration l ret (ProcedureName pl pn) ps bctx@(TemplateContext _ mb) ann s) = withInCtx (isJust mb) $ withKind PKind $ defaultInline $ do
    (ps',ret',vars',bctx',tret,vret) <- tcAddDeps l "tcProcedureDecl" $ do
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        bctx' <- tcTemplateContext bctx
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        vret <- case ret' of
            ReturnType _ Nothing -> return Nothing
            ReturnType _ (Just _) -> do
                let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
                newVariable LocalScope True True vr Nothing
                return $ Just vr
        return (ps',ret',vars',bctx',tret,vret)
    hdeps <- getDeps
    ann' <- tcProcedureAnns ann
    mapM_ dropLocalVar vret
    s' <- tcStmtsRet l tret s
    cl <- getDecClass
    let tproc = IDecT $ ProcType (locpos l) (PIden $ mkVarId pn) vars' tret (map (fmap (fmap locpos)) ann') (Just $ map (fmap (fmap locpos)) s') cl
    let proc' = ProcedureName (Typed pl tproc) $ PIden $ mkVarId pn
    let bdecctx = (\(DecCtxT x) -> x) $ typed $ loc bctx'
    proc'' <- addProc explicitDecCtx bdecctx hdeps proc'
    dec2ProcDecl l $ unDecT $ typed $ loc proc''

tcProcedureAnns :: ProverK loc m => [ProcedureAnnotation Identifier loc] -> TcM m [ProcedureAnnotation GIdentifier (Typed loc)]
tcProcedureAnns xs = do
    (inlines,anns') <- mapAndUnzipM tcProcedureAnn xs
    case catMaybes inlines of
        [] -> return ()
        is -> chgDecClassM $ chgInlineDecClass (last is)
    return anns'

tcProcedureAnn :: ProverK loc m => ProcedureAnnotation Identifier loc -> TcM m (Maybe Bool,ProcedureAnnotation GIdentifier (Typed loc))
tcProcedureAnn (PDecreasesAnn l e) = tcAddDeps l "pann" $ insideAnnotation $ withLeak False $ do
    (e') <- tcAnnExpr e
    return (Nothing,PDecreasesAnn (Typed l $ typed $ loc e') e')
tcProcedureAnn (RequiresAnn l isFree isLeak e) = tcAddDeps l "pann" $ insideAnnotation $ do
    (isLeak',e') <- checkLeak l isLeak $ tcAnnGuard e
    return (Nothing,RequiresAnn (Typed l $ typed $ loc e') isFree isLeak' e')
tcProcedureAnn (EnsuresAnn l isFree isLeak e) = tcAddDeps l "pann" $ insideAnnotation $ do
    (isLeak',e') <- checkLeak l isLeak $ tcAnnGuard e
    return (Nothing,EnsuresAnn (Typed l $ typed $ loc e') isFree isLeak' e')
tcProcedureAnn (InlineAnn l isInline) = tcAddDeps l "pann" $ do
    return (Just isInline,InlineAnn (notTyped "inline" l) isInline)

tcProcedureParam :: (ProverK loc m) => ProcedureParameter Identifier loc -> TcM m (ProcedureParameter GIdentifier (Typed loc),(Bool,Var,IsVariadic))
tcProcedureParam (ProcedureParameter l False s isVariadic (VarName vl vi)) = do
    s' <- tcTypeSpec s isVariadic True
    let ty = typed $ loc s'
    vi' <- addConst LocalScope (True,False) False vi
    let v' = VarName (Typed vl ty) vi'
    isAnn <- getAnn
    newVariable LocalScope False isAnn v' Nothing
    return (ProcedureParameter (notTyped "tcProcedureParam" l) False s' isVariadic v',(False,(fmap typed v'),isVariadic))
tcProcedureParam (ProcedureParameter l True s isVariadic (VarName vl vi)) = do
    s' <- limitExprC PureExpr $ tcTypeSpec s isVariadic True
    let ty = typed $ loc s'
    vi' <- addConst LocalScope (True,False) False vi
    let v' = VarName (Typed vl ty) vi'
    isAnn <- getAnn
    newVariable LocalScope True isAnn v' Nothing
    return (ProcedureParameter (notTyped "tcProcedureParam" l) True s' isVariadic v',(True,(fmap typed v'),isVariadic))

tcStructureDecl :: (ProverK loc m) => (DecCtx -> DecCtx -> Deps -> TypeName GIdentifier (Typed loc) -> TcM m (TypeName GIdentifier (Typed loc)))
                -> StructureDeclaration Identifier loc -> TcM m (StructureDeclaration GIdentifier (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l (TypeName tl tn) bctx@(TemplateContext _ mb) atts) = withInCtx (isJust mb) $ withKind TKind $ defaultInline $ do
    hdeps <- getDeps
    bctx' <- tcTemplateContext bctx
    let bdecctx = (\(DecCtxT x) -> x) $ typed $ loc bctx'
    atts' <- mapM tcAttribute atts
    cl <- getDecClass
    let t = IDecT $ StructType (locpos l) (TIden $ mkVarId tn) (Just $ map (fmap typed) atts') cl
    let ty' = TypeName (Typed tl t) $ TIden $ mkVarId tn
    ty'' <- addStruct explicitDecCtx bdecctx hdeps ty'
    dec2StructDecl l $ unDecT $ typed $ loc ty''

tcAttribute :: (ProverK loc m) => Attribute Identifier loc -> TcM m (Attribute GIdentifier (Typed loc))
tcAttribute (Attribute l ty (AttributeName vl vn) szs) = do
    ty' <- tcTypeSpec ty False False
    (t,szs') <- tcTypeSizes l (typed $ loc ty') szs
    let v' = AttributeName (Typed vl t) $ TIden $ mkVarId vn
    return $ Attribute (Typed vl t) ty' v' szs'

tcTemplateContext :: ProverK loc m => TemplateContext Identifier loc -> TcM m (TemplateContext GIdentifier (Typed loc))
tcTemplateContext (TemplateContext l Nothing) = return $ TemplateContext (Typed l $ DecCtxT implicitDecCtx) Nothing
tcTemplateContext (TemplateContext l (Just ks)) = onFrees l $ do
    ks' <- mapM tcContextConstraint ks
    let ts = map (Loc (locpos l) . (\(TCstrT x) -> x) . typed . loc) ks'
    frees <- getFrees l
    let dict = PureTDict (Graph.mkGraph (mkLNodes ts) []) emptyTSubsts mempty
    return $ TemplateContext (Typed l $ DecCtxT $ DecCtx True dict frees) (Just ks')

mkLNodes :: [a] -> [LNode a]
mkLNodes = zip [1..]

tcContextConstraint :: ProverK loc m => ContextConstraint Identifier loc -> TcM m (ContextConstraint GIdentifier (Typed loc))
tcContextConstraint (ContextPDec l cl isLeak isAnn ck ret (ProcedureName nl n) ts ps) = do
    ret' <- tcRetTypeSpec ret
    let n' = ProcedureName (notTyped "tcContextConstraint" l) $ PIden $ mkVarId n
    ts' <- mapM (mapM (tcVariadicArg tcTemplateTypeArgument)) ts
    (tps,ps') <- mapAndUnzipM tcCtxPArg ps
    st <- getCstrState
    let st' = st { cstrExprC = cl, cstrIsLeak = isLeak, cstrIsAnn = isAnn, cstrDecK = cstrKind2DecKind ck }
    dec <- newDecVar False Nothing
    let k = PDec False (PIden $ mkVarId n) (fmap (map (mapFst (typed . loc))) ts') tps (typed $ loc ret') dec
    let kt = TCstrT $ TcK k st'
    return $ ContextPDec (Typed l kt) cl isLeak isAnn ck ret' n' ts' ps'
tcContextConstraint (ContextODec l cl isLeak isAnn ck ret o ts ps) = do
    ret' <- tcRetTypeSpec ret
    o' <- tcOp o
    ts' <- mapM (mapM (tcVariadicArg tcTemplateTypeArgument)) ts
    (tps,ps') <- mapAndUnzipM tcCtxPArg ps
    st <- getCstrState
    let st' = st { cstrExprC = cl, cstrIsLeak = isLeak, cstrIsAnn = isAnn, cstrDecK = cstrKind2DecKind ck }
    dec <- newDecVar False Nothing
    let k = PDec False (OIden $ fmap typed o') (fmap (map (mapFst (typed . loc))) ts') tps (typed $ loc ret') dec
    let kt = TCstrT $ TcK k st'
    return $ ContextODec (Typed l kt) cl isLeak isAnn ck ret' o' ts' ps'
tcContextConstraint (ContextTDec l cl (TypeName nl n) ts) = do
    let n' = TypeName (notTyped "tcContextConstraint" l) $ TIden $ mkVarId n
    ts' <- mapM (tcVariadicArg tcTemplateTypeArgument) ts
    st <- getCstrState
    let st' = st { cstrExprC = cl, cstrDecK = TKind }
    dec <- newDecVar False Nothing
    let k = TDec False (TIden $ mkVarId n) (map (mapFst (typed . loc)) ts') dec
    let kt = TCstrT $ TcK k st'
    return $ ContextTDec (Typed l kt) cl n' ts'

tcCtxPArg :: ProverK loc m => CtxPArg Identifier loc -> TcM m ((IsConst,Either Expr Type,IsVariadic),CtxPArg GIdentifier (Typed loc))
tcCtxPArg (CtxExprPArg l isConst e isVariadic) = do
    let tcConst = if isConst then withExprC PureExpr else id
    (e',isVariadic') <- tcConst $ tcVariadicArg tcExpr (e,isVariadic)
    let t = typed $ loc e'
    return ((isConst,Left $ fmap typed e',isVariadic'),CtxExprPArg (Typed l $ IdxT $ fmap typed e') isConst e' isVariadic')
tcCtxPArg (CtxTypePArg l isConst t isVariadic) = do
    let tcConst = if isConst then withExprC PureExpr else id
    t' <- tcConst $ tcTypeSpec t isVariadic True
    let tt = typed $ loc t'
    return ((isConst,Right tt,isVariadic),CtxTypePArg (Typed l tt) isConst t' isVariadic)
tcCtxPArg (CtxVarPArg l isConst v isVariadic) = do
    let tcConst = if isConst then withExprC PureExpr else id
    v'@(TemplateArgName vl' vn') <- tcConst $ do
        isAnn <- getAnn
        isLeak <- getLeak
        checkTemplateArg (const True) isAnn isLeak (bimap mkVarId id v)
    let varn' = VarName vl' vn'
    let vart' = typed vl'
    let v'' = case typeClass "tcCtxParg" vart' of
                ExprC TypeC -> Left $ varExpr $ fromJustNote "tcCtxPArg" $ typeToVarName vart'
                VArrayC TypeC -> Left $ varExpr $ fromJustNote "tcCtxPArg" $ typeToVarName vart'
                otherwise -> Right vart'
    return ((isConst,v'',isVariadic),CtxVarPArg (Typed l $ either IdxT id v'') isConst v' isVariadic)

tcTemplateDecl :: (ProverK loc m) => TemplateDeclaration Identifier loc -> TcM m (TemplateDeclaration GIdentifier (Typed loc))
tcTemplateDecl (TemplateStructureDeclaration l targs s) = tcTemplate l $ do
    (targs',tvars') <- tcAddDeps l "tcTemplateDecl struct" $ do
        (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
        let tvars' = toList tvars
        return (targs',tvars')
    s' <- tcStructureDecl (addTemplateStruct tvars') s
    return $ TemplateStructureDeclaration (notTyped "tcTemplateDecl" l) targs' s'
tcTemplateDecl (TemplateStructureSpecialization l targs tspecials s) = tcTemplate l $ do
    (targs',tvars') <- tcAddDeps l "tcTemplateDecl structs" $ do
        (targs',tvars) <-  mapAndUnzipM tcTemplateQuantifier targs
        let tvars' = toList tvars
        return (targs',tvars')
    tspecials' <- tcAddDeps l "tcTemplateDecl structs specs" $ mapM (tcVariadicArg tcTemplateTypeArgument) tspecials
    let tspecs = map (mapFst (typed . loc)) tspecials'
    (s') <- tcStructureDecl (addTemplateStructSpecialization tvars' tspecs) s
    return $ TemplateStructureSpecialization (notTyped "tcTemplateDecl" l) targs' tspecials' s'
tcTemplateDecl (TemplateProcedureDeclaration l targs p) = tcTemplate l $ do
    (targs',tvars') <- tcAddDeps l "tcTemplateDecl proc" $ do
        (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
        let tvars' = toList tvars
        return (targs',tvars')
    (p') <- tcProcedureDecl (addTemplateOperator tvars') (addTemplateProcedureFunction tvars') p
    return $ TemplateProcedureDeclaration (notTyped "tcTemplateDecl" l) targs' p'
tcTemplateDecl (TemplateFunctionDeclaration l targs p) = tcTemplate l $ do
    (targs',tvars') <- tcAddDeps l "tcTemplateDecl fun" $ do
        (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
        let tvars' = toList tvars
        return (targs',tvars')
    (p') <- tcFunctionDecl (addTemplateOperator tvars') (addTemplateProcedureFunction tvars') p
    return $ TemplateFunctionDeclaration (notTyped "tcTemplateDecl" l) targs' p'

-- for axioms we create tokens instead of variables
tcTemplateQuantifier :: (ProverK loc m) => TemplateQuantifier Identifier loc -> TcM m (TemplateQuantifier GIdentifier (Typed loc),(Constrained Var,IsVariadic))
tcTemplateQuantifier (KindQuantifier l kClass isVariadic (KindName dl dn)) = do
    inTplt <- State.gets inTemplate
    let t = KType kClass
    t' <- mkVariadicTyArray isVariadic True t
    vdn <- addConst LocalScope (False,False) False dn
    let v' = KindName (Typed dl t') vdn
    isAnn <- getAnn
    newKindVariable isAnn LocalScope v'
    let vn = VarName t' vdn
    addTpltTok l vn
    return (KindQuantifier (notTyped "tcTemplateQuantifier" l) kClass isVariadic v',(Constrained vn Nothing,isVariadic))
tcTemplateQuantifier (DomainQuantifier l isVariadic (DomainName dl dn) mbk) = do
    inTplt <- State.gets inTemplate
    isAnn <- getAnn
    (mbk',t) <- case mbk of
        Just k -> do -- domain variable of kind @k@
            let vk = bimap mkVarId id k
            vk' <- checkKind isAnn vk
            return (Just vk',typed $ loc vk')
        Nothing -> do
            (_,(Constrained k _,_)) <- tcTemplateQuantifier $ KindQuantifier l Nothing isVariadic (KindName dl "K")
            return (Nothing,varNameToType k)
            --k <- kindToken Nothing
            --addTpltTok l $ fromJustNote "tcTemplateKind" $ typeToVarName $ KindT k
            --return (Nothing,KindT k)
    t' <- mkVariadicTyArray isVariadic True t
    vdn <- addConst LocalScope (False,False) False dn
    let v' = DomainName (Typed dl t') vdn
    newDomainVariable isAnn LocalScope v'
    let vn = VarName t' vdn
    addTpltTok l vn
    return (DomainQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v' mbk',(Constrained vn Nothing,isVariadic))
tcTemplateQuantifier (DimensionQuantifier l isVariadic (VarName dl dn) c) = do
    inTplt <- State.gets inTemplate
    let t = BaseT index -- variable is a dimension
    t' <- mkVariadicTyArray isVariadic True t
    vdn <- addConst LocalScope (False,False) False dn
    let tl = Typed dl t'
    let v' = VarName tl vdn
    isAnn <- getAnn
    newVariable LocalScope True isAnn v' Nothing
    let vn = VarName t' vdn
    addTpltTok l vn
    (c',cstrsc) <- tcWithCstrs l "tcTemplateQuantifier" $ mapM tcIndexCond c
    case c' of
        Nothing -> return ()
        Just x -> tryAddHypothesis l "tcTemplateQuantifier dim cond" LocalScope (const True) cstrsc $ HypCondition $ fmap typed x
    return (DimensionQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v' c',(Constrained vn $ fmap (fmap typed) c',isVariadic))
tcTemplateQuantifier (DataQuantifier l dClass isVariadic (TypeName tl tn)) = do
    inTplt <- State.gets inTemplate
    let t = BType dClass -- variable of any base type
    t' <- mkVariadicTyArray isVariadic True t
    vtn <- addConst LocalScope (False,False) False tn
    let v' = TypeName (Typed tl t') vtn
    isAnn <- getAnn
    isLeak <- getLeak
    newTypeVariable isAnn isLeak LocalScope v'
    let vn = VarName t' vtn
    addTpltTok l vn
    return (DataQuantifier (notTyped "tcTemplateQuantifier" l) dClass isVariadic v',(Constrained vn Nothing,isVariadic))

-- we don't allow backtracking inside templates, because there are more than two options, e.g., public domain, private domain, and token domain.
tcTemplate :: (ProverK loc m) => loc -> TcM m a -> TcM m a
tcTemplate l m = {- localOptsTcM (\opts -> opts { backtrack = BacktrackNone }) $ -} do
    oldst <- State.get
    State.modify $ \env -> env { inTemplate = Just ([],False) }
    x <- m
    updateHeadTDict l "tcTemplate" $ \_ -> return ((),emptyTDict)
    State.modify $ \env -> env { inTemplate = inTemplate oldst }
    return x

-- | TypeChecks a global declaration. At the end, forgets local declarations and solves pending constraints
tcGlobal :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> TcM m a -> TcM m a
tcGlobal l m = do
    State.modify $ \e -> e { decClass = DecClass False False (Left False) (Left False) }
    newDict l "tcGlobal"
    x <- m
    --debugTc $ liftIO $ putStrLn $ "solving tcGlobal " ++ pprid (locpos l)
    solveTop l "tcGlobal"
    dict <- top . tDict =<< State.get
    --debugTc $ do
    --    pprd <- ppr dict
    --    liftIO $ putStrLn $ "substituting tcGlobal " ++ pprid (locpos l) ++ "\n" ++ pprd
    x' <- substFromTDict "tcGlobal" dontStop l dict False Map.empty x
--    liftIO $ putStrLn $ "tcGlobal: " ++ ppr x' ++ "\n" ++ show (ppTSubsts $ tSubsts dict)
    State.modify $ \e -> e { cstrCache = Map.empty, openedCstrs = [], decClass = DecClass False False (Left False) (Left False), localConsts = Map.empty, localVars = Map.empty, localFrees = Map.empty, localDeps = Set.empty, tDict = [], moduleCount = incModuleBlock (moduleCount e) }
    liftIO resetGlobalEnv
    liftIO resetTyVarId
    return x'
  where
    top [x] = return x
    top xs = do
        ppxs <- mapM pp xs
        error $ "tcGlobal: " ++ show (vcat ppxs)

incModuleBlock :: (Maybe (Identifier,TyVarId),Int) -> (Maybe (Identifier,TyVarId),Int)
incModuleBlock = mapFst (fmap (mapSnd inc))
    where inc (TyVarId j) = TyVarId (succ j)
