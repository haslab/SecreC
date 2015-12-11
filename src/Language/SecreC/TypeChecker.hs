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
import Language.SecreC.Utils
import Language.SecreC.Vars
import Language.SecreC.Pretty

import Prelude hiding (mapM)

import Data.Bifunctor
import Data.Generics
import Data.Traversable
import Data.Foldable
import qualified Data.Map as Map

import Control.Monad hiding (mapM,mapAndUnzipM)
import Control.Monad.IO.Class
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State

import Text.PrettyPrint

tcModule :: (VarsTcM loc,Location loc) => Module Identifier loc -> TcM loc (Module VarIdentifier (Typed loc))
tcModule (Module l name prog) = do
    prog' <- tcProgram prog
    return $ Module (notTyped "tcModule" l) (fmap (bimap mkVarId (notTyped "tcModule")) name) prog'

tcProgram :: (VarsTcM loc,Location loc) => Program Identifier loc -> TcM loc (Program VarIdentifier (Typed loc))
tcProgram (Program loc imports globals) = do
    let imports' = map (bimap mkVarId (notTyped "tcProgram")) imports
    globals' <- mapM (tcGlobal loc . tcGlobalDeclaration) globals
    return $ Program (notTyped "tcProgram" loc) imports' globals'

tcGlobalDeclaration :: (VarsTcM loc,Location loc) => GlobalDeclaration Identifier loc -> TcM loc (GlobalDeclaration VarIdentifier (Typed loc))
tcGlobalDeclaration (GlobalVariable l vd) = do
    vd' <- tcVarDecl GlobalScope vd
    return $ GlobalVariable (notTyped "tcGlobalDeclaration" l) vd'
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

tcDomainDecl :: Location loc => DomainDeclaration Identifier loc -> TcM loc (DomainDeclaration VarIdentifier (Typed loc))
tcDomainDecl (Domain l d@(DomainName dl dn) k) = do
    let vk = bimap mkVarId id k
    let t = SType $ PrivateKind $ Just $ fmap (const ()) vk
    let d' = DomainName (Typed dl t) $ mkVarId dn
    newDomain d'
    checkKind vk
    return $ Domain (notTyped "tcDomainDecl" l) d' (bimap mkVarId (notTyped "tcDomainDecl") k)

tcKindDecl :: Location loc => KindDeclaration Identifier loc -> TcM loc (KindDeclaration VarIdentifier (Typed loc))
tcKindDecl (Kind l k) = do
    k' <- tcKindName k
    newKind k'
    return $ Kind (Typed l KType) k'
    
tcKindName :: Location loc => KindName Identifier loc -> TcM loc (KindName VarIdentifier (Typed loc))
tcKindName (KindName kl kn) = return $ KindName (Typed kl KType) $ mkVarId kn

tcProcedureDecl :: (VarsTcM loc,Location loc) => (Op VarIdentifier (Typed loc) -> TcM loc ()) -> (ProcedureName VarIdentifier (Typed loc) -> TcM loc ())
                -> ProcedureDeclaration Identifier loc -> TcM loc (ProcedureDeclaration VarIdentifier (Typed loc))
tcProcedureDecl addOp addProc dec@(OperatorDeclaration l ret op ps s) = do
    top <- tcOp op
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    ps' <- mapM tcProcedureParam ps
    (s',StmtType st) <- tcStmts tret s
    tcTopCstrM l $ IsReturnStmt st tret (bimap mkVarId locpos dec)
    i <- newTyVarId
    let tproc = DecT $ ProcType i (locpos l) (Right $ fmap typed top) (map (fmap typed . procedureParameterName) ps') tret $ map (fmap (fmap locpos)) s'
    let op' = updLoc top (Typed l tproc)
    addOp op'
    return $ OperatorDeclaration (notTyped "tcProcedureDecl" l) ret' op' ps' s'
tcProcedureDecl addOp addProc dec@(ProcedureDeclaration l ret proc@(ProcedureName pl pn) ps s) = do
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    ps' <- mapM tcProcedureParam ps
    (s',StmtType st) <- tcStmts tret s
    tcTopCstrM l $ IsReturnStmt st tret (bimap mkVarId locpos dec)
    let vars = map (fmap typed . procedureParameterName) ps'
    i <- newTyVarId
    let tproc = DecT $ ProcType i (locpos l) (Left $ ProcedureName () $ mkVarId pn) vars tret $ map (fmap (fmap locpos)) s'
    let proc' = ProcedureName (Typed pl tproc) $ mkVarId pn
    addProc proc'
    return $ ProcedureDeclaration (notTyped "tcProcedureDecl" l) ret' proc' ps' s'

tcProcedureParam :: (VarsTcM loc,Location loc) => ProcedureParameter Identifier loc -> TcM loc (ProcedureParameter VarIdentifier (Typed loc))
tcProcedureParam (ProcedureParameter l s v) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    let vv = bimap mkVarId id v
    let v' = fmap (flip Typed t) vv
    newVariable LocalScope v' NoValue
    return $ ProcedureParameter (notTyped "tcProcedureParam" l) s' v'

tcStructureDecl :: (VarsTcM loc,Location loc) => (TypeName VarIdentifier (Typed loc) -> TcM loc ())
                -> StructureDeclaration Identifier loc -> TcM loc (StructureDeclaration VarIdentifier (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l ty@(TypeName tl tn) atts) = do
    atts' <- mapM tcAttribute atts
    i <- newTyVarId
    let t = DecT $ StructType i (locpos l) (TypeName () $ mkVarId tn) $ map (fmap typed) atts'
    let ty' = TypeName (Typed tl t) $ mkVarId tn
    addStruct ty'
    return $ StructureDeclaration (notTyped "tcStructureDecl" l) ty' atts'

tcAttribute :: (VarsTcM loc,Location loc) => Attribute Identifier loc -> TcM loc (Attribute VarIdentifier (Typed loc))
tcAttribute (Attribute l ty v@(AttributeName vl vn)) = do
    ty' <- tcTypeSpec ty
    let t = typed $ loc ty'
    let v' = AttributeName (Typed vl t) $ mkVarId vn
    return $ Attribute (notTyped "tcAttribute" l) ty' v'

tcTemplateDecl :: (VarsTcM loc,Location loc) => TemplateDeclaration Identifier loc -> TcM loc (TemplateDeclaration VarIdentifier (Typed loc))
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
    s' <- tcStructureDecl (addTemplateStructSpecialization tvars' tspecs) s
    return $ TemplateStructureSpecialization (notTyped "tcTemplateDecl" l) targs' tspecials' s'
tcTemplateDecl (TemplateProcedureDeclaration l targs p) = tcTemplate $ do
    (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    p' <- tcProcedureDecl (addTemplateOperator tvars') (addTemplateProcedure tvars') p
    return $ TemplateProcedureDeclaration (notTyped "tcTemplateDecl" l) targs' p'
    
tcTemplateQuantifier :: Location loc => TemplateQuantifier Identifier loc -> TcM loc (TemplateQuantifier VarIdentifier (Typed loc),VarName VarIdentifier Type)
tcTemplateQuantifier (DomainQuantifier l v@(DomainName dl dn) mbk) = do
    (mbk,dk) <- case mbk of
        Just k -> do -- domain variable of kind @k@
            k' <- tcKindName k
            let vk = bimap mkVarId id k
            checkKind vk
            return (Just k',PrivateKind $ Just $ fmap (const ()) vk)
        Nothing -> do -- domain variable of any kind
            return (Nothing,AnyKind)
    let t = SType dk
    let vdn = mkVarId dn
    let v' = DomainName (Typed dl t) vdn
    newDomainVariable LocalScope v'
    return (DomainQuantifier (notTyped "tcTemplateQuantifier" l) v' mbk,VarName t vdn)
tcTemplateQuantifier (DimensionQuantifier l v@(VarName dl dn)) = do
    let t = BaseT index -- variable is a dimension
    let vdn = mkVarId dn
    let v' = VarName (Typed dl t) vdn
    newVariable LocalScope v' NoValue
    return (DimensionQuantifier (notTyped "tcTemplateQuantifier" l) v',VarName t vdn)
tcTemplateQuantifier (DataQuantifier l v@(TypeName tl tn)) = do
    let t = BType -- variable of any base type
    let vtn = mkVarId tn
    let v' = TypeName (Typed tl t) vtn
    newTypeVariable LocalScope v'
    return (DataQuantifier (notTyped "tcTemplateQuantifier" l) v',VarName t vtn)

tcTemplate :: (VarsTcM loc,Location loc) => TcM loc a -> TcM loc a
tcTemplate m = do
    x <- m
    updateHeadTDict $ \d -> return ((),mempty)
    return x

-- | TypeChecks a global declaration. At the end, forgets local declarations and solves pending constraints
tcGlobal :: (VarsTcM loc,Location loc) => loc -> TcM loc a -> TcM loc a
tcGlobal l m = do
    newDict l
    x <- m
    solve
    State.modify $ \e -> e { localVars = Map.empty, tDict = updDict (tDict e) }
    return x
  where
    updDict (ConsNe x xs) = updHeadNe (`mappend` x) xs
