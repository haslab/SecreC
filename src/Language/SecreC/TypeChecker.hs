{-# LANGUAGE ViewPatterns, DeriveDataTypeable #-}

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
import Language.SecreC.Utils
import Language.SecreC.Vars

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

tcModule :: (Vars loc,Location loc) => Module Identifier loc -> TcM loc (Module VarIdentifier (Typed loc))
tcModule (Module l name prog) = do
    prog' <- tcProgram prog
    return $ Module (notTyped l) (fmap (bimap mkVarId notTyped) name) prog'

tcProgram :: (Vars loc,Location loc) => Program Identifier loc -> TcM loc (Program VarIdentifier (Typed loc))
tcProgram (Program loc imports globals) = do
    let imports' = map (bimap mkVarId notTyped) imports
    globals' <- mapM (tcGlobal loc . tcGlobalDeclaration) globals
    return $ Program (notTyped loc) imports' globals'

tcGlobalDeclaration :: (Vars loc,Location loc) => GlobalDeclaration Identifier loc -> TcM loc (GlobalDeclaration VarIdentifier (Typed loc))
tcGlobalDeclaration (GlobalVariable l vd) = do
    vd' <- tcVarDecl GlobalScope vd
    return $ GlobalVariable (notTyped l) vd'
tcGlobalDeclaration (GlobalDomain l dd) = do
    dd' <- tcDomainDecl dd
    return $ GlobalDomain (notTyped l) dd'
tcGlobalDeclaration (GlobalKind l kd) = do
    kd' <- tcKindDecl kd
    return $ GlobalKind (notTyped l) kd'
tcGlobalDeclaration (GlobalProcedure l pd) = do
    pd' <- tcProcedureDecl newOperator newProcedure pd
    return $ GlobalProcedure (notTyped l) pd'
tcGlobalDeclaration (GlobalStructure l sd) = do
    sd' <- tcStructureDecl newStruct sd
    return $ GlobalStructure (notTyped l) sd'
tcGlobalDeclaration (GlobalTemplate l td) = do
    td' <- tcTemplateDecl td
    return $ GlobalTemplate (notTyped l) td'

tcDomainDecl :: Location loc => DomainDeclaration Identifier loc -> TcM loc (DomainDeclaration VarIdentifier (Typed loc))
tcDomainDecl (Domain l d@(DomainName dl dn) k) = do
    let vk = bimap mkVarId id k
    let t = DType $ Just $ fmap (const ()) vk
    let d' = DomainName (Typed dl t) $ mkVarId dn
    newDomain d'
    checkKind vk
    return $ Domain (notTyped l) d' (bimap mkVarId notTyped k)

tcKindDecl :: Location loc => KindDeclaration Identifier loc -> TcM loc (KindDeclaration VarIdentifier (Typed loc))
tcKindDecl (Kind l k) = do
    k' <- tcKindName k
    newKind k'
    return $ Kind (Typed l KType) k'
    
tcKindName :: Location loc => KindName Identifier loc -> TcM loc (KindName VarIdentifier (Typed loc))
tcKindName (KindName kl kn) = return $ KindName (Typed kl KType) $ mkVarId kn

tcProcedureDecl :: (Vars loc,Location loc) => (Op (Typed loc) -> TcM loc ()) -> (ProcedureName VarIdentifier (Typed loc) -> TcM loc ())
                -> ProcedureDeclaration Identifier loc -> TcM loc (ProcedureDeclaration VarIdentifier (Typed loc))
tcProcedureDecl addOp addProc dec@(OperatorDeclaration l ret op ps s) = do
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    ps' <- mapM tcProcedureParam ps
    (s',StmtType st) <- tcStmts tret s
    tcCstrM l $ IsReturnStmt st tret (bimap mkVarId locpos dec)
    i <- newTyVarId
    let tproc = ProcType i (locpos l) (map (fmap typed . procedureParameterName) ps') tret $ map (fmap (fmap locpos)) s'
    let op' = fmap (\l -> Typed l tproc) op
    addOp op'
    return $ OperatorDeclaration (notTyped l) ret' op' ps' s'
tcProcedureDecl addOp addProc dec@(ProcedureDeclaration l ret proc@(ProcedureName pl pn) ps s) = do
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    ps' <- mapM tcProcedureParam ps
    (s',StmtType st) <- tcStmts tret s
    tcCstrM l $ IsReturnStmt st tret (bimap mkVarId locpos dec)
    let vars = map (fmap typed . procedureParameterName) ps'
    i <- newTyVarId
    let tproc = ProcType i (locpos l) vars tret $ map (fmap (fmap locpos)) s'
    let proc' = ProcedureName (Typed pl tproc) $ mkVarId pn
    addProc proc'
    return $ ProcedureDeclaration (notTyped l) ret' proc' ps' s'

tcProcedureParam :: (Vars loc,Location loc) => ProcedureParameter Identifier loc -> TcM loc (ProcedureParameter VarIdentifier (Typed loc))
tcProcedureParam (ProcedureParameter l s v) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    let vv = bimap mkVarId id v
    let v' = fmap (flip Typed t) vv
    newVariable LocalScope v' NoValue
    return $ ProcedureParameter (notTyped l) s' v'

tcStructureDecl :: (Vars loc,Location loc) => (TypeName VarIdentifier (Typed loc) -> TcM loc ())
                -> StructureDeclaration Identifier loc -> TcM loc (StructureDeclaration VarIdentifier (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l ty@(TypeName tl tn) atts) = do
    atts' <- mapM tcAttribute atts
    i <- newTyVarId
    let t = StructType i (locpos l) $ map (fmap typed) atts'
    let ty' = TypeName (Typed tl t) $ mkVarId tn
    addStruct ty'
    return $ StructureDeclaration (notTyped l) ty' atts'

tcAttribute :: (Vars loc,Location loc) => Attribute Identifier loc -> TcM loc (Attribute VarIdentifier (Typed loc))
tcAttribute (Attribute l ty v@(AttributeName vl vn)) = do
    ty' <- tcTypeSpec ty
    let t = typed $ loc ty'
    let v' = AttributeName (Typed vl t) $ mkVarId vn
    return $ Attribute (notTyped l) ty' v'

tcTemplateDecl :: (Vars loc,Location loc) => TemplateDeclaration Identifier loc -> TcM loc (TemplateDeclaration VarIdentifier (Typed loc))
tcTemplateDecl (TemplateStructureDeclaration l targs s) = tcTemplateBlock $ do
    (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    s' <- tcStructureDecl (addTemplateStruct tvars') s
    return $ TemplateStructureDeclaration (notTyped l) targs' s'
tcTemplateDecl (TemplateStructureSpecialization l targs tspecials s) = tcTemplateBlock $ do
    (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    tspecials' <- mapM tcTemplateTypeArgument tspecials
    let tspecs = map (typed . loc) tspecials'
    s' <- tcStructureDecl (addTemplateStructSpecialization tvars' tspecs) s
    return $ TemplateStructureSpecialization (notTyped l) targs' tspecials' s'
tcTemplateDecl (TemplateProcedureDeclaration l targs p) = tcTemplateBlock $ do
    (targs',tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    let tvars' = toList tvars
    p' <- tcProcedureDecl (addTemplateOperator tvars') (addTemplateProcedure tvars') p
    return $ TemplateProcedureDeclaration (notTyped l) targs' p'
    
tcTemplateQuantifier :: Location loc => TemplateQuantifier Identifier loc -> TcM loc (TemplateQuantifier VarIdentifier (Typed loc),VarName VarIdentifier Type)
tcTemplateQuantifier (DomainQuantifier l v@(DomainName dl dn) mbk) = do
    (mbk,dk) <- case mbk of
        Just k -> do -- domain variable of kind @k@
            k' <- tcKindName k
            let vk = bimap mkVarId id k
            checkKind vk
            return (Just k',Just vk)
        Nothing -> do -- domain variable of any kind
            return (Nothing,Nothing)
    let t = DType $ fmap (fmap (const ())) dk
    let vdn = mkVarId dn
    let v' = DomainName (Typed dl t) vdn
    newDomainVariable LocalScope v'
    return (DomainQuantifier (notTyped l) v' mbk,VarName t vdn)
tcTemplateQuantifier (DimensionQuantifier l v@(VarName dl dn)) = do
    let t = index -- variable is a dimension
    let vdn = mkVarId dn
    let v' = VarName (Typed dl t) vdn
    newVariable LocalScope v' NoValue
    return (DimensionQuantifier (notTyped l) v',VarName t vdn)
tcTemplateQuantifier (DataQuantifier l v@(TypeName tl tn)) = do
    let t = TType -- variable of any type
    let vtn = mkVarId tn
    let v' = TypeName (Typed tl t) vtn
    newTypeVariable LocalScope v'
    return (DataQuantifier (notTyped l) v',VarName t vtn)

-- | TypeChecks a global declaration. At the end, forgets local declarations and solves pending constraints
tcGlobal :: (Vars loc,Location loc) => loc -> TcM loc a -> TcM loc a
tcGlobal l m = do
    x <- m
    solve
    State.modify $ \e -> e { localVars = Map.empty, tDict = mempty }
    return x

