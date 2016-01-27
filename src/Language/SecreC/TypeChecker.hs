{-# LANGUAGE FlexibleContexts, ViewPatterns, DeriveDataTypeable #-}

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

tcModule :: (VarsIdTcM loc m,Location loc) => Module Identifier loc -> TcM loc m (Module VarIdentifier (Typed loc))
tcModule m@(Module l name prog) = do
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
    pd' <- tcProcedureDecl newOperator newProcedure pd
    return $ GlobalProcedure (notTyped "tcGlobalDeclaration" l) pd'
tcGlobalDeclaration (GlobalStructure l sd) = do
    sd' <- tcStructureDecl newStruct sd
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

tcProcedureDecl :: (VarsIdTcM loc m,Location loc) => (Op VarIdentifier (Typed loc) -> TcM loc m ()) -> (ProcedureName VarIdentifier (Typed loc) -> TcM loc m ())
                -> ProcedureDeclaration Identifier loc -> TcM loc m (ProcedureDeclaration VarIdentifier (Typed loc))
tcProcedureDecl addOp addProc dec@(OperatorDeclaration l ret op ps s) = do
    top <- tcOp op
    (ps',vars) <- mapAndUnzipM tcProcedureParam ps
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    withCstrDependencies $ do
        (s',StmtType st) <- tcStmts tret s
        i <- newTyVarId
        let tproc = DecT $ ProcType i (locpos l) (Right $ fmap typed top) vars tret $ map (fmap (fmap locpos)) s'
        let op' = updLoc top (Typed l tproc)
        let dec' = OperatorDeclaration (notTyped "tcProcedureDecl" l) ret' op' ps' s'
        tcTopCstrM l $ IsReturnStmt st tret (fmap locpos dec')
        addOp op'
        return dec'
tcProcedureDecl addOp addProc dec@(ProcedureDeclaration l ret proc@(ProcedureName pl pn) ps s) = do
    (ps',vars) <- mapAndUnzipM tcProcedureParam ps
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    withCstrDependencies $ do
        (s',StmtType st) <- tcStmts tret s
        i <- newTyVarId
        let tproc = DecT $ ProcType i (locpos l) (Left $ ProcedureName () $ mkVarId pn) vars tret $ map (fmap (fmap locpos)) s'
        let proc' = ProcedureName (Typed pl tproc) $ mkVarId pn
        let dec' = ProcedureDeclaration (notTyped "tcProcedureDecl" l) ret' proc' ps' s'
        tcTopCstrM l $ IsReturnStmt st tret (fmap locpos dec')
        addProc proc'
        return dec'

tcProcedureParam :: (VarsIdTcM loc m,Location loc) => ProcedureParameter Identifier loc -> TcM loc m (ProcedureParameter VarIdentifier (Typed loc),(Bool,Cond (VarName VarIdentifier Type)))
tcProcedureParam (ProcedureParameter l s v sz) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    ty <- typeToComplexType l t
    (ty',sz') <- tcTypeSizes l ty (Just v) sz
    let vv = bimap mkVarId id v
    let v' = fmap (flip Typed $ ComplexT ty') vv
    newVariable LocalScope v' Nothing False
    return (ProcedureParameter (notTyped "tcProcedureParam" l) s' v' sz',(False,Cond (fmap typed v') Nothing))
tcProcedureParam (ConstProcedureParameter l s v sz c) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    ty <- typeToComplexType l t
    (ty',sz') <- tcTypeSizes l ty (Just v) sz
    let vv = bimap mkVarId id v
    let v' = fmap (flip Typed $ ComplexT ty') vv
    newVariable LocalScope v' Nothing True
    (c',cstrsc) <- tcWithCstrs l $ mapM tcIndexCond c
    case c' of
        Nothing -> return ()
        Just x -> do
            tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed x
    return (ConstProcedureParameter (notTyped "tcProcedureParam" l) s' v' sz' c',(True,Cond (fmap typed v') (fmap (fmap typed) c')))

tcStructureDecl :: (VarsIdTcM loc m,Location loc) => (TypeName VarIdentifier (Typed loc) -> TcM loc m ())
                -> StructureDeclaration Identifier loc -> TcM loc m (StructureDeclaration VarIdentifier (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l ty@(TypeName tl tn) atts) = withCstrDependencies $ do
    atts' <- mapM tcAttribute atts
    i <- newTyVarId
    let t = DecT $ StructType i (locpos l) (TypeName () $ mkVarId tn) $ map (flip Cond Nothing . fmap typed) atts'
    let ty' = TypeName (Typed tl t) $ mkVarId tn
    addStruct ty'
    return $ StructureDeclaration (notTyped "tcStructureDecl" l) ty' atts'

tcAttribute :: (VarsIdTcM loc m,Location loc) => Attribute Identifier loc -> TcM loc m (Attribute VarIdentifier (Typed loc))
tcAttribute (Attribute l ty v@(AttributeName vl vn)) = do
    ty' <- tcTypeSpec ty
    let t = typed $ loc ty'
    let v' = AttributeName (Typed vl t) $ mkVarId vn
    return $ Attribute (notTyped "tcAttribute" l) ty' v'

tcTemplateDecl :: (VarsIdTcM loc m,Location loc) => TemplateDeclaration Identifier loc -> TcM loc m (TemplateDeclaration VarIdentifier (Typed loc))
tcTemplateDecl (TemplateStructureDeclaration l targs s) = tcTemplate $ do
    (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    s' <- tcStructureDecl (addTemplateStruct tvars') s
    return $ TemplateStructureDeclaration (notTyped "tcTemplateDecl" l) targs' s'
tcTemplateDecl (TemplateStructureSpecialization l targs tspecials s) = tcTemplate $ do
    (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    tspecials' <- mapM tcTemplateTypeArgument tspecials
    let tspecs = map (typed . loc) tspecials'
    forM_ (zip tvars tspecs) $ \(ct,st) -> tcCstrM l $ Unifies (condVarNameToType ct) st
    s' <- tcStructureDecl (addTemplateStructSpecialization tvars' tspecs) s
    return $ TemplateStructureSpecialization (notTyped "tcTemplateDecl" l) targs' tspecials' s'
tcTemplateDecl (TemplateProcedureDeclaration l targs p) = tcTemplate $ do
    (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    p' <- tcProcedureDecl (addTemplateOperator tvars') (addTemplateProcedure tvars') p
    return $ TemplateProcedureDeclaration (notTyped "tcTemplateDecl" l) targs' p'
    
tcTemplateQuantifier :: (VarsIdTcM loc m,Location loc) => TemplateQuantifier Identifier loc -> TcM loc m (TemplateQuantifier VarIdentifier (Typed loc),Cond (VarName VarIdentifier Type))
tcTemplateQuantifier (DomainQuantifier l v@(DomainName dl dn) mbk) = do
    (mbk,dk) <- case mbk of
        Just k -> do -- domain variable of kind @k@
            k' <- tcKindName k
            let vk = bimap mkVarId id k
            checkKind vk
            return (Just k',PrivateKind $ Just $ funit vk)
        Nothing -> do -- domain variable of any kind
            return (Nothing,AnyKind)
    let t = SType dk
    let vdn = mkVarId dn
    let v' = DomainName (Typed dl t) vdn
    newDomainVariable LocalScope v'
    return (DomainQuantifier (notTyped "tcTemplateQuantifier" l) v' mbk,Cond (VarName t vdn) Nothing)
tcTemplateQuantifier (DimensionQuantifier l v@(VarName dl dn) c) = do
    let t = BaseT index -- variable is a dimension
    let vdn = mkVarId dn
    let tl = Typed dl t
    let v' = VarName tl vdn
    newVariable LocalScope v' Nothing True
    (c',cstrsc) <- tcWithCstrs l $ mapM tcIndexCond c
    case c' of
        Nothing -> return ()
        Just x -> tryAddHypothesis l LocalScope cstrsc $ HypCondition $ fmap typed x
    return (DimensionQuantifier (notTyped "tcTemplateQuantifier" l) v' c',Cond (VarName t vdn) $ fmap (fmap typed) c')
tcTemplateQuantifier (DataQuantifier l v@(TypeName tl tn)) = do
    let t = BType -- variable of any base type
    let vtn = mkVarId tn
    let v' = TypeName (Typed tl t) vtn
    newTypeVariable LocalScope v'
    return (DataQuantifier (notTyped "tcTemplateQuantifier" l) v',Cond (VarName t vtn) Nothing)

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
    newDict l
    x <- m
    solve l
    State.modify $ \e -> e { localVars = Map.empty, localFrees = Set.empty, localHyps = Set.empty, tDict = updDict (tDict e) }
    liftIO resetGlobalEnv
    return x
  where
      updDict (ConsNe x xs) = xs
--    updDict (ConsNe x xs) = updHeadNe (`mappend` TDict (tCstrs x) (tChoices x) Map.empty) xs
