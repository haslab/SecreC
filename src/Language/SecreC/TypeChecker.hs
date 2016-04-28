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
import Language.SecreC.TypeChecker.Template
import Language.SecreC.Utils
import Language.SecreC.Vars
import Language.SecreC.Pretty
import Language.SecreC.Parser.PreProcessor
import Language.SecreC.Prover.Base
import Language.SecreC.Prover.Expression

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

tcModuleFile :: ProverK Position m => ModuleFile -> TcM m TypedModuleFile
tcModuleFile (Left (t,args,m)) = do
    (args',m') <- tcModuleWithPPArgs (args,m)
    return $ Left (t,args',m')
tcModuleFile (Right sci) = do
    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (mappend x y,sciEnv sci) }
    return $ Right sci

tcModuleWithPPArgs :: (ProverK loc m) => (PPArgs,Module Identifier loc) -> TcM m (PPArgs,Module VarIdentifier (Typed loc))
tcModuleWithPPArgs (ppargs,x) = localOptsTcM (`mappend` ppOptions ppargs) $ do
    x' <- tcModule x
    menv <- State.gets (snd . moduleEnv)
    TcM $ lift $ writeModuleSCI ppargs menv x
    return (ppargs,x')

tcModule :: (ProverK loc m) => Module Identifier loc -> TcM m (Module VarIdentifier (Typed loc))
tcModule m@(Module l name prog) = failTcM l $ do
    opts' <- TcM $ State.lift Reader.ask
    when (debugTypechecker opts') $
        liftIO $ hPutStrLn stderr ("Typechecking module " ++ ppr (moduleId $ fmap locpos m) ++ "...")
    -- reset module typechecking environment and increment module count
    State.modify $ \env -> env
        { moduleCount = (moduleId m,succ $ snd $ moduleCount env)
        , moduleEnv = let (x,y) = moduleEnv env in (x `mappend` y,mempty)
        , tyVarId = 0
        }
    prog' <- tcProgram prog
    -- substitute the module's environment with the module's dictionary
    --ss <- getTSubsts
    --modifyModuleEnvM $ substFromTSubsts "tcModule" l ss False Map.empty
    --State.modify $ \env -> env { tDict = [] }
    let m' = Module (notTyped "tcModule" l) (fmap (bimap mkVarId (notTyped "tcModule")) name) prog'
    --m'' <- substFromTSubsts "tcModule" l ss False Map.empty m'
    return m'

tcProgram :: (ProverK loc m) => Program Identifier loc -> TcM m (Program VarIdentifier (Typed loc))
tcProgram (Program l imports globals) = do
    let imports' = map (bimap mkVarId (notTyped "tcProgram")) imports
    globals' <- mapM (\g -> tcGlobal (loc g) (tcGlobalDeclaration g)) globals
    return $ Program (notTyped "tcProgram" l) imports' globals'

tcGlobalDeclaration :: (ProverK loc m) => GlobalDeclaration Identifier loc -> TcM m (GlobalDeclaration VarIdentifier (Typed loc))
tcGlobalDeclaration (GlobalVariable l vd) = do
    vd' <- tcVarDecl GlobalScope vd
    return $ GlobalVariable (notTyped "tcGlobalDeclaration" l) vd'
tcGlobalDeclaration (GlobalConst l vd) = do
    vd' <- tcConstDecl GlobalScope vd
    return $ GlobalConst (notTyped "tcGlobalDeclaration" l) vd'
tcGlobalDeclaration (GlobalDomain l dd) = do
    dd' <- tcDomainDecl dd
    return $ GlobalDomain (notTyped "tcGlobalDeclaration" l) dd'
tcGlobalDeclaration (GlobalKind l kd) = do
    kd' <- tcKindDecl kd
    return $ GlobalKind (notTyped "tcGlobalDeclaration" l) kd'
tcGlobalDeclaration (GlobalProcedure l pd) = do
    pd' <- tcProcedureDecl newOperator newProcedure pd
    return $ GlobalProcedure (notTyped "tcGlobalDeclaration" l) pd'
tcGlobalDeclaration (GlobalStructure l sd) = do
    sd' <- tcStructureDecl newStruct sd
    return $ GlobalStructure (notTyped "tcGlobalDeclaration" l) sd'
tcGlobalDeclaration (GlobalTemplate l td) = do
    td' <- tcTemplateDecl td
    return $ GlobalTemplate (notTyped "tcGlobalDeclaration" l) td'
tcGlobalDeclaration (GlobalAnnotations l ann) = do
    ann' <- mapM tcGlobalAnn ann
    return $ GlobalAnnotations (notTyped "tcGlobalAnnotation" l) ann'

tcGlobalAnn :: ProverK loc m => GlobalAnnotation Identifier loc -> TcM m (GlobalAnnotation VarIdentifier (Typed loc))
tcGlobalAnn (GlobalProcedureAnn l [] proc) = insideAnnotation $ do
    GlobalProcedure l' proc' <- tcGlobalDeclaration (GlobalProcedure l proc)
    return $ GlobalProcedureAnn l' [] proc'
tcGlobalAnn (GlobalProcedureAnn l targs proc) = insideAnnotation $ do
    TemplateProcedureDeclaration l' targs' proc' <- tcTemplateDecl (TemplateProcedureDeclaration l targs proc)
    return $ GlobalProcedureAnn l' targs' proc'

tcDomainDecl :: (MonadIO m,Location loc) => DomainDeclaration Identifier loc -> TcM m (DomainDeclaration VarIdentifier (Typed loc))
tcDomainDecl (Domain l (DomainName dl dn) k) = do
    let vk = bimap mkVarId id k
    let t = SType $ PrivateKind $ Just $ funit vk
    let d' = DomainName (Typed dl t) $ mkVarId dn
    newDomain d'
    checkKind vk
    return $ Domain (notTyped "tcDomainDecl" l) d' (bimap mkVarId (notTyped "tcDomainDecl") k)

tcKindDecl :: (MonadIO m,Location loc) => KindDeclaration Identifier loc -> TcM m (KindDeclaration VarIdentifier (Typed loc))
tcKindDecl (Kind l k) = do
    k' <- tcKindName k
    newKind k'
    return $ Kind (Typed l KType) k'
    
tcKindName :: (MonadIO m,Location loc) => KindName Identifier loc -> TcM m (KindName VarIdentifier (Typed loc))
tcKindName (KindName kl kn) = return $ KindName (Typed kl KType) $ mkVarId kn

tcProcedureDecl :: (ProverK loc m) => (Deps -> Op VarIdentifier (Typed loc) -> TcM m (Op VarIdentifier (Typed loc))) -> (Deps -> ProcedureName VarIdentifier (Typed loc) -> TcM m (ProcedureName VarIdentifier (Typed loc)))
                -> ProcedureDeclaration Identifier loc -> TcM m (ProcedureDeclaration VarIdentifier (Typed loc))
tcProcedureDecl addOp _ (OperatorDeclaration l ret op ps ann s) = do
    (ps',ret',vars',top,tret) <- tcAddDeps l "tcProcedureDecl" $ do
        top <- tcOp op
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        return (ps',ret',vars',top,tret)
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    (s',StmtType st) <- tcStmts tret s
    cl <- liftM procClass State.get
    let tproc = DecT $ ProcType (locpos l) (Right $ fmap typed top) vars' tret (map (fmap (fmap locpos)) ann') (map (fmap (fmap locpos)) s') cl
    let op' = updLoc top (Typed l tproc)
    tcTopCstrM l $ IsReturnStmt st tret
    op'' <- addOp hdeps op'
    let dec' = OperatorDeclaration (notTyped "tcProcedureDecl" l) ret' op'' ps' ann' s'
    return dec'
tcProcedureDecl _ addProc (ProcedureDeclaration l ret (ProcedureName pl pn) ps ann s) = do
    (ps',ret',vars',tret) <- tcAddDeps l "tcProcedureDecl" $ do
        (ps',vars') <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        return (ps',ret',vars',tret)
    hdeps <- getDeps
    ann' <- mapM tcProcedureAnn ann
    (s',StmtType st) <- tcStmts tret s
    cl <- liftM procClass State.get
    let tproc = DecT $ ProcType (locpos l) (Left $ mkVarId pn) vars' tret (map (fmap (fmap locpos)) ann') (map (fmap (fmap locpos)) s') cl
    let proc' = ProcedureName (Typed pl tproc) $ mkVarId pn
    tcTopCstrM l $ IsReturnStmt st tret
    proc'' <- addProc hdeps proc'
    let dec' = ProcedureDeclaration (notTyped "tcProcedureDecl" l) ret' proc'' ps' ann' s'
    return dec'

tcProcedureAnn :: ProverK loc m => ProcedureAnnotation Identifier loc -> TcM m (ProcedureAnnotation VarIdentifier (Typed loc))
tcProcedureAnn (RequiresAnn l e) = insideAnnotation $ do
    e' <- tcExpr e
    return $ RequiresAnn (Typed l $ typed $ loc e') e'
tcProcedureAnn (EnsuresAnn l e) = insideAnnotation $ do
    e' <- tcExpr e
    return $ EnsuresAnn (Typed l $ typed $ loc e') e'

tcProcedureParam :: (ProverK loc m) => ProcedureParameter Identifier loc -> TcM m (ProcedureParameter VarIdentifier (Typed loc),(Bool,Cond (VarName VarIdentifier Type),IsVariadic))
tcProcedureParam (ProcedureParameter l s isVariadic v) = do
    s' <- tcTypeSpec s isVariadic
    let ty = typed $ loc s'
    let (VarName vvl vvn) = bimap mkVarId id v
    let v' = VarName (Typed vvl ty) vvn
    newVariable LocalScope v' Nothing False
    return (ProcedureParameter (notTyped "tcProcedureParam" l) s' isVariadic v',(False,Cond (fmap typed v') Nothing,isVariadic))
tcProcedureParam (ConstProcedureParameter l s isVariadic (VarName vl vi) c) = do
    s' <- tcTypeSpec s isVariadic
    let ty = typed $ loc s'
    vi' <- addConst LocalScope vi
    let v' = VarName (Typed vl ty) vi'
    newVariable LocalScope v' Nothing True
    (c',cstrsc) <- tcWithCstrs l "tcProcedureParam" $ mapM tcIndexCond c
    case c' of
        Nothing -> return ()
        Just x -> do
            tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed x
    return (ConstProcedureParameter (notTyped "tcProcedureParam" l) s' isVariadic v' c',(True,Cond (fmap typed v') (fmap (fmap typed) c'),isVariadic))

tcStructureDecl :: (ProverK loc m) => (Deps -> TypeName VarIdentifier (Typed loc) -> TcM m (TypeName VarIdentifier (Typed loc)))
                -> StructureDeclaration Identifier loc -> TcM m (StructureDeclaration VarIdentifier (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l (TypeName tl tn) atts) = do
    hdeps <- getDeps
    atts' <- mapM tcAttribute atts
    let t = DecT $ StructType (locpos l) (TypeName () $ mkVarId tn) $ map (flip Cond Nothing . fmap typed) atts'
    let ty' = TypeName (Typed tl t) $ mkVarId tn
    ty'' <- addStruct hdeps ty'
    return $ StructureDeclaration (notTyped "tcStructureDecl" l) ty'' atts'

tcAttribute :: (ProverK loc m) => Attribute Identifier loc -> TcM m (Attribute VarIdentifier (Typed loc))
tcAttribute (Attribute l ty (AttributeName vl vn)) = do
    ty' <- tcTypeSpec ty False
    let t = typed $ loc ty'
    let v' = AttributeName (Typed vl t) $ mkVarId vn
    return $ Attribute (notTyped "tcAttribute" l) ty' v'

tcTemplateDecl :: (ProverK loc m) => TemplateDeclaration Identifier loc -> TcM m (TemplateDeclaration VarIdentifier (Typed loc))
tcTemplateDecl (TemplateStructureDeclaration l targs s) = tcTemplate $ do
    (targs',tvars) <- tcAddDeps l "tcTemplateDecl" $ mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    s' <- tcStructureDecl (addTemplateStruct tvars') s
    return $ TemplateStructureDeclaration (notTyped "tcTemplateDecl" l) targs' s'
tcTemplateDecl (TemplateStructureSpecialization l targs tspecials s) = tcTemplate $ do
    (targs',tvars) <- tcAddDeps l "tcTemplateDecl" $ mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    tspecials' <- tcAddDeps l "tcTemplateDecl" $ mapM (tcVariadicArg tcTemplateTypeArgument) tspecials
    let tspecs = map (mapFst (typed . loc)) tspecials'
    s' <- tcStructureDecl (addTemplateStructSpecialization tvars' tspecs) s
    return $ TemplateStructureSpecialization (notTyped "tcTemplateDecl" l) targs' tspecials' s'
tcTemplateDecl (TemplateProcedureDeclaration l targs p) = tcTemplate $ do
    (targs',tvars) <- tcAddDeps l "tcTemplateDecl" $ mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    p' <- tcProcedureDecl (addTemplateOperator tvars') (addTemplateProcedure tvars') p
    return $ TemplateProcedureDeclaration (notTyped "tcTemplateDecl" l) targs' p'
    
tcTemplateQuantifier :: (ProverK loc m) => TemplateQuantifier Identifier loc -> TcM m (TemplateQuantifier VarIdentifier (Typed loc),(Cond (VarName VarIdentifier Type),IsVariadic))
tcTemplateQuantifier (DomainQuantifier l isVariadic (DomainName dl dn) mbk) = do
    (mbk',dk') <- case mbk of
        Just k -> do -- domain variable of kind @k@
            k' <- tcKindName k
            let vk = bimap mkVarId id k
            checkKind vk
            return (Just k',PrivateKind $ Just $ funit vk)
        Nothing -> do -- domain variable of any kind
            return (Nothing,AnyKind)
    let t = SType dk'
    t' <- mkVariadicTyArray isVariadic t
    let vdn = mkVarId dn
    let v' = DomainName (Typed dl t') vdn
    newDomainVariable LocalScope v'
    return (DomainQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v' mbk',(Cond (VarName t' vdn) Nothing,isVariadic))
tcTemplateQuantifier (DimensionQuantifier l isVariadic (VarName dl dn) c) = do
    let t = BaseT index -- variable is a dimension
    t' <- mkVariadicTyArray isVariadic t
    let vdn = mkVarId dn
    let tl = Typed dl t'
    let v' = VarName tl vdn
    newVariable LocalScope v' Nothing True
    (c',cstrsc) <- tcWithCstrs l "tcTemplateQuantifier" $ mapM tcIndexCond c
    case c' of
        Nothing -> return ()
        Just x -> tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed x
    return (DimensionQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v' c',(Cond (VarName t' vdn) $ fmap (fmap typed) c',isVariadic))
tcTemplateQuantifier (DataQuantifier l isVariadic (TypeName tl tn)) = do
    let t = BType -- variable of any base type
    t' <- mkVariadicTyArray isVariadic t
    let vtn = mkVarId tn
    let v' = TypeName (Typed tl t') vtn
    newTypeVariable LocalScope v'
    return (DataQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v',(Cond (VarName t' vtn) Nothing,isVariadic))

tcTemplate :: (ProverK Position m) => TcM m a -> TcM m a
tcTemplate m = do
    State.modify $ \env -> env { inTemplate = True }
    x <- m
    updateHeadTDict $ \_ -> return ((),mempty)
    State.modify $ \env -> env { inTemplate = False }
    return x

-- | TypeChecks a global declaration. At the end, forgets local declarations and solves pending constraints
tcGlobal :: (Vars VarIdentifier (TcM m) a,ProverK loc m) => loc -> TcM m a -> TcM m a
tcGlobal l m = do
    State.modify $ \e -> e { procClass = mempty }
    newDict l "tcGlobal"
    x <- m
    solve l
    dict <- liftM ((\[a] -> a) . tDict) State.get
    x' <- substFromTDict "tcGlobal" l dict False Map.empty x
--    liftIO $ putStrLn $ "tcGlobal: " ++ ppr x' ++ "\n" ++ show (ppTSubsts $ tSubsts dict)
    State.modify $ \e -> e { procClass = mempty, localConsts = Map.empty, localVars = Map.empty, localFrees = Set.empty, localDeps = Set.empty, tDict = [] }
    liftIO resetGlobalEnv
    return x'
