{-# LANGUAGE ViewPatterns, DeriveDataTypeable #-}

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
import Language.SecreC.Utils

import Prelude hiding (mapM)

import Data.Generics
import Data.Traversable
import Data.Foldable

import Control.Monad hiding (mapM,mapAndUnzipM)

tcModule :: Location loc => Module loc -> TcM loc (Module (Typed loc))
tcModule (Module l name prog) = do
    prog' <- tcProgram prog
    return $ Module (notTyped l) (fmap (fmap notTyped) name) prog'

tcProgram :: Location loc => Program loc -> TcM loc (Program (Typed loc))
tcProgram (Program loc imports globals) = do
    let imports' = map (fmap notTyped) imports
    globals' <- mapM (tcGlobal . tcGlobalDeclaration) globals
    return $ Program (notTyped loc) imports' globals'

tcGlobalDeclaration :: Location loc => GlobalDeclaration loc -> TcM loc (GlobalDeclaration (Typed loc))
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

tcDomainDecl :: Location loc => DomainDeclaration loc -> TcM loc (DomainDeclaration (Typed loc))
tcDomainDecl (Domain l d@(DomainName dl dn) k) = do
    let t = DType $ Just $ kindId k
    let d' = DomainName (Typed dl t) dn
    newDomain d'
    checkKind k
    return $ Domain (notTyped l) d' (fmap notTyped k)

tcKindDecl :: Location loc => KindDeclaration loc -> TcM loc (KindDeclaration (Typed loc))
tcKindDecl (Kind l k) = do
    k' <- tcKindName k
    newKind k'
    return $ Kind (Typed l KType) k'
    
tcKindName :: Location loc => KindName loc -> TcM loc (KindName (Typed loc))
tcKindName (KindName kl kn) = return $ KindName (Typed kl KType) kn

tcProcedureDecl :: Location loc => (Op (Typed loc) -> TcM loc ()) -> (ProcedureName (Typed loc) -> TcM loc ())
                -> ProcedureDeclaration loc -> TcM loc (ProcedureDeclaration (Typed loc))
tcProcedureDecl addOp addProc (OperatorDeclaration l ret op ps s) = do
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    ps' <- mapM tcProcedureParam ps
    (s',st) <- tcStmts tret s
    when (not $ isReturnStmtType st) $ tcError (locpos l) $ NoReturnStatement (Left $ fmap locpos op)
    let tproc = ProcType (map (fmap typed . procedureParameterName) ps') tret
    let op' = fmap (\l -> Typed l tproc) op
    addOp op'
    return $ OperatorDeclaration (notTyped l) ret' op' ps' s'
tcProcedureDecl addOp addProc (ProcedureDeclaration l ret proc@(ProcedureName pl pn) ps s) = do
    ret' <- tcRetTypeSpec ret
    let tret = typed $ loc ret'
    ps' <- mapM tcProcedureParam ps
    (s',st) <- tcStmts tret s
    when (not $ isReturnStmtType st) $ tcError (locpos l) $ NoReturnStatement (Right $ fmap locpos proc)
    let tproc = ProcType (map (fmap typed . procedureParameterName) ps') tret
    let proc' = ProcedureName (Typed pl tproc) pn
    addProc proc'
    return $ ProcedureDeclaration (notTyped l) ret' proc' ps' s'

tcProcedureParam :: Location loc => ProcedureParameter loc -> TcM loc (ProcedureParameter (Typed loc))
tcProcedureParam (ProcedureParameter l s v) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    let v' = fmap (flip Typed t) v
    return $ ProcedureParameter (notTyped l) s' v'

tcStructureDecl :: Location loc => (TypeName (Typed loc) -> TcM loc ())
                -> StructureDeclaration loc -> TcM loc (StructureDeclaration (Typed loc))
tcStructureDecl addStruct (StructureDeclaration l ty@(TypeName tl tn) atts) = do
    atts' <- mapM tcAttribute atts
    let t = StructType $ map (fmap typed) atts'
    let ty' = TypeName (Typed tl t) tn
    addStruct ty'
    return $ StructureDeclaration (notTyped l) ty' atts'

tcAttribute :: Location loc => Attribute loc -> TcM loc (Attribute (Typed loc))
tcAttribute (Attribute l ty v@(AttributeName vl vn)) = do
    ty' <- tcTypeSpec ty
    let t = typed $ loc ty'
    let v' = AttributeName (Typed vl t) vn
    newField v'
    return $ Attribute (notTyped l) ty' v'

--tcTemplateTypeArgument :: Location loc => TemplateTypeArgument loc -> TcM loc (TemplateTypeArgument (Typed loc))

tcTemplateDecl :: Location loc => TemplateDeclaration loc -> TcM loc (TemplateDeclaration (Typed loc))
tcTemplateDecl (TemplateStructureDeclaration l targs s) = tcTemplateTypeBlock $ do
    (targs',toList -> tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    s' <- tcStructureDecl (addTemplateStruct tvars) s
    return $ TemplateStructureDeclaration (notTyped l) targs' s'
tcTemplateDecl (TemplateStructureSpecialization l targs tspecials s) = tcTemplateTypeBlock $ do
    (targs',toList -> tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    tspecials' <- mapM tcTemplateTypeArgument tspecials
    let tspecs = map (typed . loc) tspecials'
    s' <- tcStructureDecl (addTemplateStructSpecialization tvars tspecs) s
    return $ TemplateStructureSpecialization (notTyped l) targs' tspecials' s'
tcTemplateDecl (TemplateProcedureDeclaration l targs p) = do
    (targs',toList -> tvars) <- mapAndUnzipM tcTemplateQuantifier targs
    p' <- tcProcedureDecl (addTemplateOperator tvars) (addTemplateProcedure tvars) p
    return $ TemplateProcedureDeclaration (notTyped l) targs' p'
    
tcTemplateQuantifier :: Location loc => TemplateQuantifier loc -> TcM loc (TemplateQuantifier (Typed loc),Typed Identifier)
tcTemplateQuantifier (DomainQuantifier l v@(DomainName dl dn) mbk) = do
    (mbk,dk) <- case mbk of
        Just k -> do -- domain variable of kind @k@
            k' <- tcKindName k
            checkKind k
            return (Just k',Just $ kindId k)
        Nothing -> do -- domain variable of any kind
            return (Nothing,Nothing)
    let t = DType dk
    let v' = DomainName (Typed dl t) dn
    newDomainVariable LocalScope v'
    return (DomainQuantifier (notTyped l) v' mbk,Typed dn t)
tcTemplateQuantifier (DimensionQuantifier l v@(VarName dl dn)) = do
    let t = largestInt -- variable is a dimension
    let v' = VarName (Typed dl t) dn
    newVariable LocalScope v'
    return (DimensionQuantifier (notTyped l) v',Typed dn t)
tcTemplateQuantifier (DataQuantifier l v@(TypeName tl tn)) = do
    let t = TType -- variable of any type
    let v' = TypeName (Typed tl t) tn
    newTypeVariable LocalScope v'
    return (DataQuantifier (notTyped l) v',Typed tn t)



