{-# LANGUAGE ConstraintKinds #-}

module Language.SecreC.Transformation.Default where

import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Modules
import Language.SecreC.Position

import Control.Monad
import Control.Monad.State (StateT(..),evalStateT)
import qualified Control.Monad.State as State

import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Generics

type DefaultK m = Monad m
type DefaultM m = StateT (Set Identifier) m

defaultModuleFile :: DefaultK m => ModuleFile -> m ModuleFile
defaultModuleFile (Right x) = return $ Right x
defaultModuleFile (Left (x,y,m,ml)) = do
    m' <- defaultModule m
    return $ Left (x,y,m',ml)

defaultModule :: Monad m => Module Identifier Position -> m (Module Identifier Position)
defaultModule (Module l mn p) = do
    p' <- defaultProgram p
    return $ Module l mn p'

defaultProgram :: Monad m => Program Identifier Position -> m (Program Identifier Position)
defaultProgram (Program l is gs) = do
    gs' <- liftM concat $ mapM defaultGlobalDecl gs
    return $ Program l is gs'

defaultGlobalDecl :: DefaultK m => GlobalDeclaration Identifier Position -> m [GlobalDeclaration Identifier Position]
defaultGlobalDecl g@(GlobalStructure l s) = do
    g' <- liftM (GlobalProcedure l) $ evalStateT (defaultConstructor [] s) Set.empty
    return [g,g']
defaultGlobalDecl g@(GlobalTemplate l (TemplateStructureDeclaration sl qs s)) = do
    let targs = map templateQuantifier2Arg qs
    g' <- liftM (GlobalTemplate l . TemplateProcedureDeclaration sl qs) $ evalStateT (defaultConstructor targs s) Set.empty
    return [g,g']
defaultGlobalDecl g = return [g]

defaultVar :: DefaultK m => Identifier -> DefaultM m Identifier
defaultVar s = do
    vs <- State.get
    if Set.member s vs
        then defaultVar (s++"1")
        else do
            State.modify $ Set.insert s
            return s

templateQuantifier2Arg :: TemplateQuantifier Identifier Position -> (TemplateTypeArgument Identifier Position,IsVariadic)
templateQuantifier2Arg (DomainQuantifier l isVariadic (DomainName dl dn) _) = (GenericTemplateTypeArgument l $ TemplateArgName dl dn,isVariadic)
templateQuantifier2Arg (KindQuantifier l isPriv isVariadic (KindName kl kn)) = (GenericTemplateTypeArgument l $ TemplateArgName kl kn,isVariadic)
templateQuantifier2Arg (DimensionQuantifier l isVariadic v _) = (ExprTemplateTypeArgument l $ RVariablePExpr l v,isVariadic)
templateQuantifier2Arg (DataQuantifier l dataClass isVariadic (TypeName tl tn)) = (GenericTemplateTypeArgument l $ TemplateArgName tl tn,isVariadic)

defaultConstructor :: DefaultK m => [(TemplateTypeArgument Identifier Position,IsVariadic)] -> StructureDeclaration Identifier Position -> DefaultM m (ProcedureDeclaration Identifier Position)
defaultConstructor targs (StructureDeclaration l (TypeName tl tn) (TemplateContext cl _) atts) = do
    State.modify $ \xs -> Set.union xs $ Set.insert tn $ Set.fromList $ map (attributeNameId . attributeName) atts 
    let ty = TypeSpecifier l Nothing (TemplateSpecifier l (TypeName tl tn) targs) Nothing
    let ret = ReturnType l $ Just ty
    body <- defaultConstructorBody l ty atts
    let inline = InlineAnn l True
    return $ ProcedureDeclaration l ret (ProcedureName tl tn) [] (TemplateContext cl Nothing) [inline] body 
    
defaultConstructorBody :: DefaultK m => Position -> TypeSpecifier Identifier Position -> [Attribute Identifier Position] -> DefaultM m [Statement Identifier Position]
defaultConstructorBody l ty atts = do
    v <- liftM (VarName l) $ defaultVar "def"
    let e = RVariablePExpr l v
    let def = VarStatement l $ VariableDeclaration l False True ty $ WrapNe $ VariableInitialization l v Nothing Nothing
    let bind (Attribute l t a@(AttributeName al an) szs) = do
        x <- liftM (VarName l) $ defaultVar $ "defx"++an
        let defx = VarStatement l $ VariableDeclaration l False False t $ WrapNe $ VariableInitialization l x szs Nothing
        let bin = ExpressionStatement l $ BinaryAssign l (SelectionExpr l e a) (BinaryAssignEqual l) (RVariablePExpr l x)
        return [defx,bin]
    binds <- liftM concat $ mapM bind atts
    let ret = ReturnStatement l $ Just e
    return $ [def] ++ binds ++ [ret]

