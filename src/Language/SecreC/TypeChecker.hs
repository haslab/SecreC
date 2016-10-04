{-# LANGUAGE TupleSections, FlexibleContexts, ViewPatterns, DeriveDataTypeable #-}

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
    x' <- tcModule x
    menv <- State.gets (snd . moduleEnv)
    TcM $ lift $ writeModuleSCI ppargs menv x
    return (ppargs,x')

tcModule :: (ProverK loc m) => Module Identifier loc -> TcM m (Module GIdentifier (Typed loc))
tcModule m@(Module l name prog) = failTcM l $ do
    opts' <- TcM $ State.lift Reader.ask
    when (debugTypechecker opts') $ do
        ppm <- ppr (moduleId $ fmap locpos m)
        liftIO $ hPutStrLn stderr ("Typechecking module " ++ ppm ++ "...")
    -- reset module typechecking environment and increment module count
    State.modify $ \env -> env
        { moduleCount = ((moduleId m,TyVarId 0),succ $ snd $ moduleCount env)
        , moduleEnv = let (x,y) = moduleEnv env in (x `mappend` y,mempty)
        }
    liftIO resetTyVarId
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
    pd' <- tcProcedureDecl (newOperator) newProcedureFunction pd
    return $ GlobalProcedure (notTyped "tcGlobalDeclaration" l) pd'
tcGlobalDeclaration (GlobalFunction l pd) = tcGlobal l $ do
    pd' <- tcFunctionDecl (newOperator) newProcedureFunction pd
    return $ GlobalFunction (notTyped "tcGlobalDeclaration" l) pd'
tcGlobalDeclaration (GlobalStructure l sd) = tcGlobal l $ do
    sd' <- tcStructureDecl newStruct sd
    return $ GlobalStructure (notTyped "tcGlobalDeclaration" l) sd'
tcGlobalDeclaration (GlobalTemplate l td) = tcGlobal l $ do
    td' <- tcTemplateDecl td
    return $ GlobalTemplate (notTyped "tcGlobalDeclaration" l) td'
tcGlobalDeclaration (GlobalAnnotations l ann) = do
    ann' <- mapM tcGlobalAnn ann
    return $ GlobalAnnotations (notTyped "tcGlobalAnnotation" l) ann'

tcGlobalAnn :: ProverK loc m => GlobalAnnotation Identifier loc -> TcM m (GlobalAnnotation GIdentifier (Typed loc))
tcGlobalAnn (GlobalFunctionAnn l proc) = tcGlobal l $ insideAnnotation $ do
    proc' <- tcFunctionDecl (newOperator) newProcedureFunction proc
    return $ GlobalFunctionAnn (notTyped "tcGlobalAnn" l) proc'
tcGlobalAnn (GlobalProcedureAnn l proc) = tcGlobal l $ insideAnnotation $ do
    proc' <- tcProcedureDecl (newOperator) newProcedureFunction proc
    return $ GlobalProcedureAnn (notTyped "tcGlobalAnn" l) proc'
tcGlobalAnn (GlobalStructureAnn l proc) = tcGlobal l $ insideAnnotation $ do
    proc' <- tcStructureDecl newStruct proc
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
tcAxiomDecl (AxiomDeclaration l isLeak qs ps ann) = withKind AKind $ withLeak isLeak $ do
    (tvars',vars') <- tcAddDeps l "tcAxiomDecl" $ do
        (qs',tvars') <- mapAndUnzipM tcTemplateQuantifier qs
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        return (tvars',vars')
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    cl <- getDecClass Nothing
    let idec = AxiomType isLeak (locpos l) vars' (map (fmap (fmap locpos)) ann') cl
    dec <- newAxiom l hdeps tvars' idec
    dec2AxiomDecl l dec

tcLemmaDecl :: ProverK loc m => LemmaDeclaration Identifier loc -> TcM m (LemmaDeclaration GIdentifier (Typed loc))
tcLemmaDecl (LemmaDeclaration l isLeak n@(ProcedureName pl pn) qs ps ann body) = tcTemplate l $ withKind LKind $ withLeak isLeak $ do
    (tvars',vars') <- tcAddDeps l "tcAxiomDecl" $ do
        (qs',tvars') <- mapAndUnzipM tcTemplateQuantifier qs
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        return (tvars',vars')
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    let tret = ComplexT Void
    s' <- mapM (tcStmtsRet l tret) body
    cl <- getDecClass $ Just $ PIden $ mkVarId pn
    let idec = IDecT $ LemmaType isLeak (locpos l) (PIden $ mkVarId pn) vars' (map (fmap (fmap locpos)) ann') (fmap (map (fmap (fmap locpos))) s') cl
    let lemma' = ProcedureName (Typed pl idec) $ PIden $ mkVarId pn
    lemma'' <- newLemma tvars' hdeps lemma'
    dec2LemmaDecl l $ unDecT $ typed $ loc lemma''

tcFunctionDecl :: (ProverK loc m) => (Deps -> Op GIdentifier (Typed loc) -> TcM m (Op GIdentifier (Typed loc))) -> (Deps -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc)))
                -> FunctionDeclaration Identifier loc -> TcM m (FunctionDeclaration GIdentifier (Typed loc))
tcFunctionDecl addOp _ (OperatorFunDeclaration l isLeak ret op ps ann s) = withKind FKind $ withLeak isLeak $ do
    (ps',ret',vars',top,tret,vret) <- tcAddDeps l "tcProcedureDecl" $ do
        top <- tcOp op
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcTypeSpec ret False
        let tret = typed $ loc ret'
        when isLeak $ tcCstrM_ l $ Unifies tret (BaseT bool)
        vret <- do
            let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
            newVariable LocalScope True True vr Nothing
            return vr
        return (ps',ret',vars',top,tret,vret)
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    s' <- tcExprTy tret s
    dropLocalVar vret
    cl <- getDecClass $ Just $ OIden $ bimap id (const ()) top
    let tproc = IDecT $ FunType isLeak (locpos l) (OIden $ fmap typed top) vars' tret (map (fmap (fmap locpos)) ann') (Just $ fmap (fmap locpos) s') cl
    let op' = updLoc top (Typed l tproc)
    op'' <- addOp hdeps op'
    dec2FunDecl l $ unDecT $ typed $ loc op''
    --return $ OperatorFunDeclaration (notTyped "tcProcedureDecl" l) ret' op'' ps' ann' s'
tcFunctionDecl _ addProc (FunDeclaration l isLeak ret (ProcedureName pl pn) ps ann s) = withKind FKind $ withLeak isLeak $ do
    (ps',ret',vars',tret,vret) <- tcAddDeps l "tcProcedureDecl" $ do
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcTypeSpec ret False
        let tret = typed $ loc ret'
        when isLeak $ tcCstrM_ l $ Unifies tret (BaseT bool)
        vret <- do
            let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
            newVariable LocalScope True True vr Nothing
            return vr
        return (ps',ret',vars',tret,vret)
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    s' <- tcExprTy tret s
    dropLocalVar vret
    cl <- getDecClass $ Just $ PIden $ mkVarId pn
    let tproc = IDecT $ FunType isLeak (locpos l) (PIden $ mkVarId pn) vars' tret (map (fmap (fmap locpos)) ann') (Just $ fmap (fmap locpos) s') cl
    let proc' = ProcedureName (Typed pl tproc) $ PIden $ mkVarId pn
    proc'' <- addProc hdeps proc'
    dec2FunDecl l $ unDecT $ typed $ loc proc''
    --return $ FunDeclaration (notTyped "tcProcedureDecl" l) ret' proc'' ps' ann' s'

tcProcedureDecl :: (ProverK loc m) => (Deps -> Op GIdentifier (Typed loc) -> TcM m (Op GIdentifier (Typed loc))) -> (Deps -> ProcedureName GIdentifier (Typed loc) -> TcM m (ProcedureName GIdentifier (Typed loc)))
                -> ProcedureDeclaration Identifier loc -> TcM m (ProcedureDeclaration GIdentifier (Typed loc))
tcProcedureDecl addOp _ (OperatorDeclaration l ret op ps ann s) = withKind PKind $ do
    (ps',ret',vars',top,tret,vret) <- tcAddDeps l "tcProcedureDecl" $ do
        top <- tcOp op
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        vret <- case ret' of
            ReturnType _ Nothing -> return Nothing
            ReturnType _ (Just _) -> do
                let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
                newVariable LocalScope True True vr Nothing
                return $ Just vr
        return (ps',ret',vars',top,tret,vret)
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    mapM_ dropLocalVar vret
    s' <- tcStmtsRet l tret s
    cl <- getDecClass $ Just $ OIden $ bimap id (const ()) top
    let tproc = IDecT $ ProcType (locpos l) (OIden $ fmap typed top) vars' tret (map (fmap (fmap locpos)) ann') (Just $ map (fmap (fmap locpos)) s') cl
    let op' = updLoc top (Typed l tproc)
    op'' <- addOp hdeps op'
    dec2ProcDecl l $ unDecT $ typed $ loc op''
    --return $ OperatorDeclaration (notTyped "tcProcedureDecl" l) ret' op'' ps' ann' s'
tcProcedureDecl _ addProc (ProcedureDeclaration l ret (ProcedureName pl pn) ps ann s) = withKind PKind $ do
    (ps',ret',vars',tret,vret) <- tcAddDeps l "tcProcedureDecl" $ do
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        vret <- case ret' of
            ReturnType _ Nothing -> return Nothing
            ReturnType _ (Just _) -> do
                let vr = (VarName (Typed l tret) (VIden $ mkVarId "\\result"))
                newVariable LocalScope True True vr Nothing
                return $ Just vr
        return (ps',ret',vars',tret,vret)
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    mapM_ dropLocalVar vret
    s' <- tcStmtsRet l tret s
    cl <- getDecClass $ Just $ PIden $ mkVarId pn
    let tproc = IDecT $ ProcType (locpos l) (PIden $ mkVarId pn) vars' tret (map (fmap (fmap locpos)) ann') (Just $ map (fmap (fmap locpos)) s') cl
    let proc' = ProcedureName (Typed pl tproc) $ PIden $ mkVarId pn
    proc'' <- addProc hdeps proc'
    dec2ProcDecl l $ unDecT $ typed $ loc proc''
    --return $ ProcedureDeclaration (notTyped "tcProcedureDecl" l) ret' proc'' ps' ann' s'

tcProcedureAnn :: ProverK loc m => ProcedureAnnotation Identifier loc -> TcM m (ProcedureAnnotation GIdentifier (Typed loc))
tcProcedureAnn (PDecreasesAnn l e) = tcAddDeps l "pann" $ insideAnnotation $ withLeak False $ do
    (e') <- tcAnnExpr e
    return $ PDecreasesAnn (Typed l $ typed $ loc e') e'
tcProcedureAnn (RequiresAnn l isFree isLeak e) = tcAddDeps l "pann" $ insideAnnotation $ do
    (isLeak',e') <- checkLeak l isLeak $ tcAnnGuard e
    return $ RequiresAnn (Typed l $ typed $ loc e') isFree isLeak' e'
tcProcedureAnn (EnsuresAnn l isFree isLeak e) = tcAddDeps l "pann" $ insideAnnotation $ do
    (isLeak',e') <- checkLeak l isLeak $ tcAnnGuard e
    return $ EnsuresAnn (Typed l $ typed $ loc e') isFree isLeak' e'
tcProcedureAnn (InlineAnn l isInline) = tcAddDeps l "pann" $ do
    addDecClass $ DecClass False isInline Map.empty Map.empty
    return $ InlineAnn (notTyped "inline" l) isInline

tcProcedureParam :: (ProverK loc m) => ProcedureParameter Identifier loc -> TcM m (ProcedureParameter GIdentifier (Typed loc),(Bool,Var,IsVariadic))
tcProcedureParam (ProcedureParameter l False s isVariadic (VarName vl vi)) = do
    s' <- tcTypeSpec s isVariadic
    let ty = typed $ loc s'
    vi' <- addConst LocalScope False False vi
    let v' = VarName (Typed vl ty) vi'
    isAnn <- getAnn
    newVariable LocalScope False isAnn v' Nothing
    return (ProcedureParameter (notTyped "tcProcedureParam" l) False s' isVariadic v',(False,(fmap typed v'),isVariadic))
tcProcedureParam (ProcedureParameter l True s isVariadic (VarName vl vi)) = do
    s' <- tcTypeSpec s isVariadic
    let ty = typed $ loc s'
    vi' <- addConst LocalScope False False vi
    let v' = VarName (Typed vl ty) vi'
    isAnn <- getAnn
    newVariable LocalScope True isAnn v' Nothing
    return (ProcedureParameter (notTyped "tcProcedureParam" l) True s' isVariadic v',(True,(fmap typed v'),isVariadic))

tcStructureDecl :: (ProverK loc m) => (Deps -> TypeName GIdentifier (Typed loc) -> TcM m (TypeName GIdentifier (Typed loc)))
                -> StructureDeclaration Identifier loc -> TcM m (StructureDeclaration GIdentifier (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l (TypeName tl tn) atts) = withKind TKind $ do
    hdeps <- getDeps
    atts' <- mapM tcAttribute atts
    cl <- getDecClass $ Just $ TIden $ mkVarId tn
    let t = IDecT $ StructType (locpos l) (TIden $ mkVarId tn) (Just $ map (fmap typed) atts') cl
    let ty' = TypeName (Typed tl t) $ TIden $ mkVarId tn
    ty'' <- addStruct hdeps ty'
    dec2StructDecl l $ unDecT $ typed $ loc ty''
    --return $ StructureDeclaration (notTyped "tcStructureDecl" l) ty'' atts'

tcAttribute :: (ProverK loc m) => Attribute Identifier loc -> TcM m (Attribute GIdentifier (Typed loc))
tcAttribute (Attribute l ty (AttributeName vl vn) szs) = do
    ty' <- tcTypeSpec ty False
    (t,szs') <- tcTypeSizes l (typed $ loc ty') szs
    let v' = AttributeName (Typed vl t) $ TIden $ mkVarId vn
    return $ Attribute (Typed vl t) ty' v' szs'

tcTemplateDecl :: (ProverK loc m) => TemplateDeclaration Identifier loc -> TcM m (TemplateDeclaration GIdentifier (Typed loc))
tcTemplateDecl (TemplateStructureDeclaration l targs s) = tcTemplate l $ do
    (targs',tvars) <- tcAddDeps l "tcTemplateDecl" $ mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    s' <- tcStructureDecl (addTemplateStruct tvars') s
    return $ TemplateStructureDeclaration (notTyped "tcTemplateDecl" l) targs' s'
tcTemplateDecl (TemplateStructureSpecialization l targs tspecials s) = tcTemplate l $ do
    (targs',tvars) <- tcAddDeps l "tcTemplateDecl" $ mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    tspecials' <- tcAddDeps l "tcTemplateDecl" $ mapM (tcVariadicArg tcTemplateTypeArgument) tspecials
    let tspecs = map (mapFst (typed . loc)) tspecials'
    s' <- tcStructureDecl (addTemplateStructSpecialization tvars' tspecs) s
    return $ TemplateStructureSpecialization (notTyped "tcTemplateDecl" l) targs' tspecials' s'
tcTemplateDecl (TemplateProcedureDeclaration l targs p) = tcTemplate l $ do
    (targs',tvars) <- tcAddDeps l "tcTemplateDecl" $ mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    p' <- tcProcedureDecl (addTemplateOperator tvars') (addTemplateProcedureFunction tvars') p
    return $ TemplateProcedureDeclaration (notTyped "tcTemplateDecl" l) targs' p'
tcTemplateDecl (TemplateFunctionDeclaration l targs p) = tcTemplate l $ do
    (targs',tvars) <- tcAddDeps l "tcTemplateDecl" $ mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    p' <- tcFunctionDecl (addTemplateOperator tvars') (addTemplateProcedureFunction tvars') p
    return $ TemplateFunctionDeclaration (notTyped "tcTemplateDecl" l) targs' p'

-- for axioms we create tokens instead of variables
tcTemplateQuantifier :: (ProverK loc m) => TemplateQuantifier Identifier loc -> TcM m (TemplateQuantifier GIdentifier (Typed loc),(Constrained Var,IsVariadic))
tcTemplateQuantifier (KindQuantifier l kClass isVariadic (KindName dl dn)) = do
    inTplt <- State.gets inTemplate
    let t = KType kClass
    t' <- mkVariadicTyArray isVariadic t
    vdn <- addConst LocalScope (not inTplt) False dn
    let v' = KindName (Typed dl t') vdn
    isAnn <- getAnn
    newKindVariable isAnn LocalScope v'
    return (KindQuantifier (notTyped "tcTemplateQuantifier" l) kClass isVariadic v',(Constrained (VarName t' vdn) Nothing,isVariadic))
tcTemplateQuantifier (DomainQuantifier l isVariadic (DomainName dl dn) mbk) = do
    inTplt <- State.gets inTemplate
    isAnn <- getAnn
    (mbk',t) <- case mbk of
        Just k -> do -- domain variable of kind @k@
            let vk = bimap mkVarId id k
            vk' <- checkKind isAnn vk
            return (Just vk',typed $ loc vk')
        Nothing -> do -- domain variable of any kind
            if inTplt
                then do
                    k@(KVar kv _) <- newKindVar "k" Nothing True Nothing
                    topTcCstrM_ l $ Resolve $ KindT k
                    return (Nothing,KindT k)
                else do
                    k <- kindToken Nothing
                    return (Nothing,KindT k)
    t' <- mkVariadicTyArray isVariadic t
    vdn <- addConst LocalScope (not inTplt) False dn
    let v' = DomainName (Typed dl t') vdn
    newDomainVariable isAnn LocalScope v'
    return (DomainQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v' mbk',(Constrained (VarName t' vdn) Nothing,isVariadic))
tcTemplateQuantifier (DimensionQuantifier l isVariadic (VarName dl dn) c) = do
    inTplt <- State.gets inTemplate
    let t = BaseT index -- variable is a dimension
    t' <- mkVariadicTyArray isVariadic t
    vdn <- addConst LocalScope (not inTplt) False dn
    let tl = Typed dl t'
    let v' = VarName tl vdn
    isAnn <- getAnn
    newVariable LocalScope True isAnn v' Nothing
    (c',cstrsc) <- tcWithCstrs l "tcTemplateQuantifier" $ mapM tcIndexCond c
    case c' of
        Nothing -> return ()
        Just x -> tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed x
    return (DimensionQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v' c',(Constrained (VarName t' vdn) $ fmap (fmap typed) c',isVariadic))
tcTemplateQuantifier (DataQuantifier l dClass isVariadic (TypeName tl tn)) = do
    inTplt <- State.gets inTemplate
    let t = BType dClass -- variable of any base type
    t' <- mkVariadicTyArray isVariadic t
    vtn <- addConst LocalScope (not inTplt) False tn
    let v' = TypeName (Typed tl t') vtn
    isAnn <- getAnn
    isLeak <- getLeak
    newTypeVariable isAnn isLeak LocalScope v'
    return (DataQuantifier (notTyped "tcTemplateQuantifier" l) dClass isVariadic v',(Constrained (VarName t' vtn) Nothing,isVariadic))

tcTemplate :: (ProverK loc m) => loc -> TcM m a -> TcM m a
tcTemplate l m = do
    State.modify $ \env -> env { inTemplate = True }
    x <- m
    updateHeadTDict l "tcTemplate" $ \_ -> return ((),emptyTDict)
    State.modify $ \env -> env { inTemplate = False }
    return x

-- | TypeChecks a global declaration. At the end, forgets local declarations and solves pending constraints
tcGlobal :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> TcM m a -> TcM m a
tcGlobal l m = do
    State.modify $ \e -> e { decClass = mempty }
    newDict l "tcGlobal"
    x <- m
    solveTop l "tcGlobal"
    dict <- top . tDict =<< State.get
    x' <- substFromTDict "tcGlobal" l dict False Map.empty x
--    liftIO $ putStrLn $ "tcGlobal: " ++ ppr x' ++ "\n" ++ show (ppTSubsts $ tSubsts dict)
    State.modify $ \e -> e { cstrCache = Map.empty, openedCstrs = [], decClass = mempty, localConsts = Map.empty, localVars = Map.empty, localFrees = Map.empty, localDeps = Set.empty, tDict = [], moduleCount = let ((m,TyVarId j),i) = moduleCount e in ((m,TyVarId $ succ j),i) }
    liftIO resetGlobalEnv
    liftIO resetTyVarId
    return x'
  where
    top [x] = return x
    top xs = do
        ppxs <- mapM pp xs
        error $ "tcGlobal: " ++ show (vcat ppxs)
