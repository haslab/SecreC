{-# LANGUAGE TupleSections, FlexibleContexts, ViewPatterns, DeriveDataTypeable #-}

-- We delay resolution of all possible constraints inside the  body of templates, even those that do not depend on template variables, to better match C++ templates that are only typechecked on full instantiation.

module Language.SecreC.TypeChecker where

import Language.SecreC.Monad
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
import Language.SecreC.TypeChecker.Index
import Language.SecreC.Utils
import Language.SecreC.Vars
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.SMT
import Language.SecreC.Parser.PreProcessor

import Prelude hiding (mapM)

import Data.Bifunctor
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
import Control.Monad.Reader (Reader(..),ReaderT(..))
import qualified Control.Monad.Reader as Reader

import Text.PrettyPrint

import System.IO

tcModuleWithPPArgs :: (VarsIdTcM loc m,Location loc) => (PPArgs,Module Identifier loc) -> TcM loc m (PPArgs,Module VarIdentifier (Typed loc))
tcModuleWithPPArgs (ppargs,x) = localOptsTcM (`mappend` ppOptions ppargs) (liftM (ppargs,) $ tcModule x)

tcModule :: (VarsIdTcM loc m,Location loc) => Module Identifier loc -> TcM loc m (Module VarIdentifier (Typed loc))
tcModule m@(Module l name prog) = failTcM l $ do
    opts <- TcM $ State.lift Reader.ask
    when (debugTypechecker opts) $
        liftIO $ hPutStrLn stderr ("Typechecking module " ++ ppr (modulePosId $ fmap locpos m) ++ "...")
    prog' <- tcProgram prog
    -- increment module count
    State.modify $ \env -> env { moduleCount = succ (moduleCount env) }
    return $ Module (notTyped "tcModule" l) (fmap (bimap mkVarId (notTyped "tcModule")) name) prog'

tcProgram :: (VarsIdTcM loc m,Location loc) => Program Identifier loc -> TcM loc m (Program VarIdentifier (Typed loc))
tcProgram (Program l imports globals) = do
    let imports' = map (bimap mkVarId (notTyped "tcProgram")) imports
    globals' <- mapM (\g -> tcGlobal (loc g) (tcGlobalDeclaration g)) globals
    return $ Program (notTyped "tcProgram" l) imports' globals'

tcGlobalDeclaration :: (VarsIdTcM loc m,Location loc) => GlobalDeclaration Identifier loc -> TcM loc m (GlobalDeclaration VarIdentifier (Typed loc))
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
    pd' <- tcProcedureDecl (newOperator) (newProcedure) pd
    return $ GlobalProcedure (notTyped "tcGlobalDeclaration" l) pd'
tcGlobalDeclaration (GlobalStructure l sd) = do
    sd' <- tcStructureDecl (newStruct) sd
    return $ GlobalStructure (notTyped "tcGlobalDeclaration" l) sd'
tcGlobalDeclaration (GlobalTemplate l td) = do
    td' <- tcTemplateDecl td
    return $ GlobalTemplate (notTyped "tcGlobalDeclaration" l) td'

tcDomainDecl :: (MonadIO m,Location loc) => DomainDeclaration Identifier loc -> TcM loc m (DomainDeclaration VarIdentifier (Typed loc))
tcDomainDecl (Domain l d@(DomainName dl dn) k) = do
    let vk = bimap mkVarId id k
    let t = SType $ PrivateKind $ Just $ funit vk
    let d' = DomainName (Typed dl t) $ mkVarId dn
    newDomain d'
    checkKind vk
    return $ Domain (notTyped "tcDomainDecl" l) d' (bimap mkVarId (notTyped "tcDomainDecl") k)

tcKindDecl :: (MonadIO m,Location loc) => KindDeclaration Identifier loc -> TcM loc m (KindDeclaration VarIdentifier (Typed loc))
tcKindDecl (Kind l k) = do
    k' <- tcKindName k
    newKind k'
    return $ Kind (Typed l KType) k'
    
tcKindName :: (MonadIO m,Location loc) => KindName Identifier loc -> TcM loc m (KindName VarIdentifier (Typed loc))
tcKindName (KindName kl kn) = return $ KindName (Typed kl KType) $ mkVarId kn

tcProcedureDecl :: (VarsIdTcM loc m,Location loc) => (Deps loc -> Op VarIdentifier (Typed loc) -> TcM loc m (Op VarIdentifier (Typed loc))) -> (Deps loc -> ProcedureName VarIdentifier (Typed loc) -> TcM loc m (ProcedureName VarIdentifier (Typed loc)))
                -> ProcedureDeclaration Identifier loc -> TcM loc m (ProcedureDeclaration VarIdentifier (Typed loc))
tcProcedureDecl addOp addProc dec@(OperatorDeclaration l ret op ps s) = do
    (ps',ret',vars,top,tret) <- tcAddDeps l "tcProcedureDecl" $ do
        top <- tcOp op
        (ps',vars) <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        return (ps',ret',vars,top,tret)
    hdeps <- getDeps
    (s',StmtType st) <- tcStmts tret s
    let tproc = DecT $ ProcType (locpos l) (Right $ fmap typed top) vars tret $ map (fmap (fmap locpos)) s'
    let op' = updLoc top (Typed l tproc)
    tcTopCstrM l $ IsReturnStmt st tret
    op'' <- addOp hdeps op'
    let dec' = OperatorDeclaration (notTyped "tcProcedureDecl" l) ret' op'' ps' s'
    return dec'
tcProcedureDecl addOp addProc dec@(ProcedureDeclaration l ret proc@(ProcedureName pl pn) ps s) = do
    (ps',ret',vars,tret) <- tcAddDeps l "tcProcedureDecl" $ do
        (ps',vars) <- mapAndUnzipM tcProcedureParam ps
        ret' <- tcRetTypeSpec ret
        let tret = typed $ loc ret'
        return (ps',ret',vars,tret)
    hdeps <- getDeps
    (s',StmtType st) <- tcStmts tret s
    let tproc = DecT $ ProcType (locpos l) (Left $ ProcedureName () $ mkVarId pn) vars tret $ map (fmap (fmap locpos)) s'
    let proc' = ProcedureName (Typed pl tproc) $ mkVarId pn
    tcTopCstrM l $ IsReturnStmt st tret
    proc'' <- addProc hdeps proc'
    let dec' = ProcedureDeclaration (notTyped "tcProcedureDecl" l) ret' proc'' ps' s'
    return dec'

tcProcedureParam :: (VarsIdTcM loc m,Location loc) => ProcedureParameter Identifier loc -> TcM loc m (ProcedureParameter VarIdentifier (Typed loc),(Bool,Cond (VarName VarIdentifier Type),IsVariadic))
tcProcedureParam (ProcedureParameter l s isVariadic v sz) = do
    s' <- tcTypeSpec s isVariadic
    let ty = typed $ loc s'
    (ty',sz') <- tcTypeSizes l ty sz
    let vv = bimap mkVarId id v
    let v' = fmap (flip Typed ty') vv
    newVariable LocalScope v' Nothing False
    return (ProcedureParameter (notTyped "tcProcedureParam" l) s' isVariadic v' sz',(False,Cond (fmap typed v') Nothing,isVariadic))
tcProcedureParam (ConstProcedureParameter l s isVariadic v@(VarName vl vi) sz c) = do
    s' <- tcTypeSpec s isVariadic
    let ty = typed $ loc s'
    (ty',sz') <- tcTypeSizes l ty sz
    vi' <- addConst LocalScope vi
    let vv = VarName vl vi'
    let v' = fmap (flip Typed ty') vv
    newVariable LocalScope v' Nothing True
    (c',cstrsc) <- tcWithCstrs l "tcProcedureParam" $ mapM tcIndexCond c
    case c' of
        Nothing -> return ()
        Just x -> do
            tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed x
    return (ConstProcedureParameter (notTyped "tcProcedureParam" l) s' isVariadic v' sz' c',(True,Cond (fmap typed v') (fmap (fmap typed) c'),isVariadic))

tcStructureDecl :: (VarsIdTcM loc m,Location loc) => (Deps loc -> TypeName VarIdentifier (Typed loc) -> TcM loc m (TypeName VarIdentifier (Typed loc)))
                -> StructureDeclaration Identifier loc -> TcM loc m (StructureDeclaration VarIdentifier (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l ty@(TypeName tl tn) atts) = do
    hdeps <- getDeps
    atts' <- mapM tcAttribute atts
    let t = DecT $ StructType (locpos l) (TypeName () $ mkVarId tn) $ map (flip Cond Nothing . fmap typed) atts'
    let ty' = TypeName (Typed tl t) $ mkVarId tn
    ty'' <- addStruct hdeps ty'
    return $ StructureDeclaration (notTyped "tcStructureDecl" l) ty'' atts'

tcAttribute :: (VarsIdTcM loc m,Location loc) => Attribute Identifier loc -> TcM loc m (Attribute VarIdentifier (Typed loc))
tcAttribute (Attribute l ty v@(AttributeName vl vn)) = do
    ty' <- tcTypeSpec ty False
    let t = typed $ loc ty'
    let v' = AttributeName (Typed vl t) $ mkVarId vn
    return $ Attribute (notTyped "tcAttribute" l) ty' v'

tcTemplateDecl :: (VarsIdTcM loc m,Location loc) => TemplateDeclaration Identifier loc -> TcM loc m (TemplateDeclaration VarIdentifier (Typed loc))
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
    
tcTemplateQuantifier :: (VarsIdTcM loc m,Location loc) => TemplateQuantifier Identifier loc -> TcM loc m (TemplateQuantifier VarIdentifier (Typed loc),(Cond (VarName VarIdentifier Type),IsVariadic))
tcTemplateQuantifier (DomainQuantifier l isVariadic v@(DomainName dl dn) mbk) = do
    (mbk,dk) <- case mbk of
        Just k -> do -- domain variable of kind @k@
            k' <- tcKindName k
            let vk = bimap mkVarId id k
            checkKind vk
            return (Just k',PrivateKind $ Just $ funit vk)
        Nothing -> do -- domain variable of any kind
            return (Nothing,AnyKind)
    let t = SType dk
    t' <- mkVariadicTyArray isVariadic t
    let vdn = mkVarId dn
    let v' = DomainName (Typed dl t') vdn
    newDomainVariable LocalScope v'
    return (DomainQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v' mbk,(Cond (VarName t' vdn) Nothing,isVariadic))
tcTemplateQuantifier (DimensionQuantifier l isVariadic v@(VarName dl dn) c) = do
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
tcTemplateQuantifier (DataQuantifier l isVariadic v@(TypeName tl tn)) = do
    let t = BType -- variable of any base type
    t' <- mkVariadicTyArray isVariadic t
    let vtn = mkVarId tn
    let v' = TypeName (Typed tl t') vtn
    newTypeVariable LocalScope v'
    return (DataQuantifier (notTyped "tcTemplateQuantifier" l) isVariadic v',(Cond (VarName t' vtn) Nothing,isVariadic))

tcTemplate :: (VarsIdTcM loc m,Location loc) => TcM loc m a -> TcM loc m a
tcTemplate m = do
    State.modify $ \env -> env { inTemplate = True }
    x <- m
    updateHeadTDict $ \d -> return ((),mempty)
    State.modify $ \env -> env { inTemplate = False }
    return x

-- | TypeChecks a global declaration. At the end, forgets local declarations and solves pending constraints
tcGlobal :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m a -> TcM loc m a
tcGlobal l m = do
    newDict l "tcGlobal"
    x <- m
    solve l
    State.modify $ \e -> e { localConsts = Map.empty, localVars = Map.empty, localFrees = Set.empty, localDeps = Set.empty, tDict = updDict (tDict e) }
    liftIO resetGlobalEnv
    return x
  where
      updDict (ConsNe x xs) = xs
