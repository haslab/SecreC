{-# LANGUAGE TypeFamilies, DeriveFoldable, DeriveTraversable, DeriveFunctor, MultiParamTypeClasses, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances #-}

module Language.SecreC.Syntax where

import Data.Traversable
import Data.Foldable
import Data.Generics hiding (empty)
import Text.PrettyPrint

import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Utils

-- Program and variable declarations:                                          

data Module loc = Module loc (Maybe (ModuleName loc)) (Program loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

moduleFile :: Location loc => Module loc -> String
moduleFile (Module l _ _) = posFileName $ locpos l

moduleId :: Module loc -> Identifier
moduleId (Module _ Nothing _) = "main"
moduleId (Module _ (Just (ModuleName _ n)) _) = n

moduleImports :: Module loc -> [ImportDeclaration loc]
moduleImports (Module _ _ p) = programImports p

instance Location loc => Located (Module loc) where
    type LocOf (Module loc) = loc
    loc (Module l _ _) = l

instance PP (Module loc) where
    pp (Module _ (Just modulename) prog) = text "module" <+> pp modulename <+> text "where" $$ pp prog
    pp (Module _ Nothing prog) = pp prog

data AttributeName loc = AttributeName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
attributeNameId :: AttributeName loc -> Identifier
attributeNameId (AttributeName _ i) = i
  
instance Location loc => Located (AttributeName loc) where
    type LocOf (AttributeName loc) = loc
    loc (AttributeName l _) = l
  
instance PP (AttributeName loc) where
    pp (AttributeName _ iden) = text iden

data ModuleName loc = ModuleName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (ModuleName loc) where
    type LocOf (ModuleName loc) = loc
    loc (ModuleName l _) = l
  
instance PP (ModuleName loc) where
    pp (ModuleName _ iden) = text iden

data TemplateArgName loc = TemplateArgName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (TemplateArgName loc) where
    type LocOf (TemplateArgName loc) = loc
    loc (TemplateArgName l _) = l
  
instance PP (TemplateArgName loc) where
    pp (TemplateArgName _ iden) = text iden

data Program loc = Program loc [ImportDeclaration loc] [GlobalDeclaration loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
programImports :: Program loc -> [ImportDeclaration loc]
programImports (Program _ is _) = is
  
instance Location loc => Located (Program loc) where
    type LocOf (Program loc) = loc
    loc (Program l _ _) = l
  
instance PP (Program loc) where
    pp (Program _ is gs) = pp is $$ pp gs

instance PP [ImportDeclaration loc] where
    pp is = vcat $ map pp is

instance PP [GlobalDeclaration loc] where
    pp gs = vcat $ map pp gs

data ImportDeclaration loc = Import loc (ModuleName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (ImportDeclaration loc) where
    type LocOf (ImportDeclaration loc) = loc
    loc (Import l _) = l
 
instance PP (ImportDeclaration loc) where
    pp (Import _ modulename) = text "import" <+> pp modulename

data GlobalDeclaration loc
    = GlobalVariable loc (VariableDeclaration loc)
    | GlobalDomain loc (DomainDeclaration loc)
    | GlobalKind loc (KindDeclaration loc)
    | GlobalProcedure loc (ProcedureDeclaration loc)
    | GlobalStructure loc (StructureDeclaration loc)
    | GlobalTemplate loc (TemplateDeclaration loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (GlobalDeclaration loc) where
    type LocOf (GlobalDeclaration loc) = loc
    loc (GlobalVariable l vd) = l
    loc (GlobalDomain l dd) = l
    loc (GlobalKind l kd) = l
    loc (GlobalProcedure l pd) = l
    loc (GlobalStructure l sd) = l
    loc (GlobalTemplate l td) = l

instance PP (GlobalDeclaration loc) where
    pp (GlobalVariable _ vd) = pp vd
    pp (GlobalDomain _ dd) = pp dd
    pp (GlobalKind _ kd) = pp kd
    pp (GlobalProcedure _ pd) = pp pd
    pp (GlobalStructure _ sd) = pp sd
    pp (GlobalTemplate _ td) = pp td

data KindDeclaration loc = Kind loc (KindName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
 
instance Location loc => Located (KindDeclaration loc) where
    type LocOf (KindDeclaration loc) = loc
    loc (Kind l _) = l
 
instance PP (KindDeclaration loc) where
    pp (Kind _ kname) = text "kind" <+> pp kname
  
data KindName loc = KindName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

kindId :: KindName loc -> Identifier
kindId (KindName _ n) = n

instance Location loc => Located (KindName loc) where
    type LocOf (KindName loc) = loc
    loc (KindName l _) = l

instance PP (KindName loc) where
    pp (KindName _ iden) = text iden

data DomainDeclaration loc = Domain loc (DomainName loc) (KindName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (DomainDeclaration loc) where
    type LocOf (DomainDeclaration loc) = loc
    loc (Domain l _ _) = l

instance PP (DomainDeclaration loc) where
    pp (Domain _ dom kind) = text "domain" <+> pp dom <+> pp kind
 
data DomainName loc = DomainName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (DomainName loc) where
    type LocOf (DomainName loc) = loc
    loc (DomainName l _) = l

instance PP (DomainName loc) where
    pp (DomainName _ iden) = pp iden

data ProcedureName loc = ProcedureName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (ProcedureName loc) where
    type LocOf (ProcedureName loc) = loc
    loc (ProcedureName l _) = l
 
instance PP (ProcedureName loc) where
    pp (ProcedureName _ iden) = text iden

data VarName loc = VarName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (VarName loc) where
    type LocOf (VarName loc) = loc
    loc (VarName l _) = l
 
instance PP (VarName loc) where
    pp (VarName _ iden) = pp iden

data TypeName loc = TypeName loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

typeId :: TypeName loc -> Identifier
typeId (TypeName _ i) = i

instance Location loc => Located (TypeName loc) where
    type LocOf (TypeName loc) = loc
    loc (TypeName l _) = l

instance PP (TypeName loc) where
    pp (TypeName _ iden) = text iden

type Identifier = String

instance PP String where
    pp s = text s

data VariableInitialization loc = VariableInitialization loc (VarName loc) (Maybe (Sizes loc)) (Maybe (Expression loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (VariableInitialization loc) where
    type LocOf (VariableInitialization loc) = loc
    loc (VariableInitialization l _ _ _) = l
 
instance PP (VariableInitialization loc) where
    pp (VariableInitialization _ v dim ex) = pp v <+> ppDim dim <+> ppExp ex
        where
        ppDim Nothing = empty
        ppDim (Just dim) = parens (pp dim)
        ppExp Nothing = empty
        ppExp (Just e) = text "=" <+> pp e

newtype Sizes loc = Sizes (NeList (Expression loc))
  deriving (Read,Show,Data,Typeable,Eq,Ord)

instance Functor Sizes where
    fmap f (Sizes xs) = Sizes $ fmap (fmap f) xs

instance Location loc => Located (Sizes loc) where
    type LocOf (Sizes loc) = loc
    loc (Sizes xs) = loc (headNe xs)

instance PP (Sizes loc) where
    pp (Sizes es) = parens (sepBy comma $ fmap pp es)

data VariableDeclaration loc = VariableDeclaration loc (TypeSpecifier loc) (NeList (VariableInitialization loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (VariableDeclaration loc) where
    type LocOf (VariableDeclaration loc) = loc
    loc (VariableDeclaration l _ _) = l

instance PP (VariableDeclaration loc) where
    pp (VariableDeclaration _ t is) = pp t <+> sepBy comma (fmap pp is)

data ProcedureParameter loc = ProcedureParameter loc (TypeSpecifier loc) (VarName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

procedureParameterName :: ProcedureParameter loc -> VarName loc
procedureParameterName (ProcedureParameter _ _ n) = n

instance Location loc => Located (ProcedureParameter loc) where
    type LocOf (ProcedureParameter loc) = loc
    loc (ProcedureParameter l _ _) = l

instance PP (ProcedureParameter loc) where
    pp (ProcedureParameter _ t v) = pp t <+> pp v

-- Types:                                                                      

data TypeSpecifier loc = TypeSpecifier loc (Maybe (SecTypeSpecifier loc)) (DatatypeSpecifier loc) (Maybe (DimtypeSpecifier loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
typeSpecifierLoc :: TypeSpecifier loc -> loc
typeSpecifierLoc (TypeSpecifier l _ _ _) = l

instance Location loc => Located (TypeSpecifier loc) where
    type LocOf (TypeSpecifier loc) = loc
    loc (TypeSpecifier l _ _ _) = l
  
instance PP (TypeSpecifier loc) where
    pp (TypeSpecifier _ sec t dim) = ppMb sec <+> pp t <+> ppMb dim

data SecTypeSpecifier loc
    = PublicSpecifier loc
    | PrivateSpecifier loc (DomainName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (SecTypeSpecifier loc) where
    type LocOf (SecTypeSpecifier loc) = loc
    loc (PublicSpecifier l) = l
    loc (PrivateSpecifier l _) = l

instance PP (SecTypeSpecifier loc) where
    pp (PublicSpecifier _) = text "public"
    pp (PrivateSpecifier _ n) = pp n

data DatatypeSpecifier loc
    = PrimitiveSpecifier loc (PrimitiveDatatype loc)
    | TemplateSpecifier loc (TypeName loc) [TemplateTypeArgument loc]
    | VariableSpecifier loc (TypeName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (DatatypeSpecifier loc) where
    type LocOf (DatatypeSpecifier loc) = loc
    loc (PrimitiveSpecifier l _) = l
    loc (TemplateSpecifier l _ _) = l
    loc (VariableSpecifier l _) = l

instance PP (DatatypeSpecifier loc) where
    pp (PrimitiveSpecifier _ prim) = pp prim
    pp (TemplateSpecifier _ t args) = pp t <> abrackets (sepBy comma $ map pp args)
    pp (VariableSpecifier _ tn) = pp tn

data PrimitiveDatatype loc
    = DatatypeBool       loc
    | DatatypeInt        loc
    | DatatypeUint       loc
    | DatatypeInt8       loc
    | DatatypeUint8      loc
    | DatatypeInt16      loc
    | DatatypeUint16     loc
    | DatatypeInt32      loc
    | DatatypeUint32     loc
    | DatatypeInt64      loc
    | DatatypeUint64     loc
    | DatatypeString     loc
    | DatatypeXorUint8   loc
    | DatatypeXorUint16  loc
    | DatatypeXorUint32  loc
    | DatatypeXorUint64  loc
    | DatatypeXorUint    loc
    | DatatypeFloat      loc
    | DatatypeFloat32    loc
    | DatatypeFloat64    loc
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (PrimitiveDatatype loc) where
    type LocOf (PrimitiveDatatype loc) = loc
    loc (DatatypeBool       l) = l
    loc (DatatypeInt        l) = l
    loc (DatatypeUint       l) = l
    loc (DatatypeInt8       l) = l
    loc (DatatypeUint8      l) = l
    loc (DatatypeInt16      l) = l
    loc (DatatypeUint16     l) = l
    loc (DatatypeInt32      l) = l
    loc (DatatypeUint32     l) = l
    loc (DatatypeInt64      l) = l
    loc (DatatypeUint64     l) = l
    loc (DatatypeString     l) = l
    loc (DatatypeXorUint8   l) = l
    loc (DatatypeXorUint16  l) = l
    loc (DatatypeXorUint32  l) = l
    loc (DatatypeXorUint64  l) = l
    loc (DatatypeXorUint    l) = l
    loc (DatatypeFloat      l) = l
    loc (DatatypeFloat32    l) = l
    loc (DatatypeFloat64    l) = l

instance PP (PrimitiveDatatype loc) where
    pp (DatatypeBool       _) = text "bool"
    pp (DatatypeInt        _) = text "int"
    pp (DatatypeUint       _) = text "uint"
    pp (DatatypeInt8       _) = text "int8"
    pp (DatatypeUint8      _) = text "uint8"
    pp (DatatypeInt16      _) = text "int16"
    pp (DatatypeUint16     _) = text "uint16"
    pp (DatatypeInt32      _) = text "int32"
    pp (DatatypeUint32     _) = text "uint32"
    pp (DatatypeInt64      _) = text "int64"
    pp (DatatypeUint64     _) = text "uint64"
    pp (DatatypeString     _) = text "string"
    pp (DatatypeXorUint8   _) = text "xor_uint8"
    pp (DatatypeXorUint16  _) = text "xor_uint16"
    pp (DatatypeXorUint32  _) = text "xor_uint32"
    pp (DatatypeXorUint64  _) = text "xor_uint64"
    pp (DatatypeXorUint    _) = text "xor_uint"
    pp (DatatypeFloat      _) = text "float"
    pp (DatatypeFloat32    _) = text "float32"
    pp (DatatypeFloat64    _) = text "float64"
  
data TemplateTypeArgument loc
    = GenericTemplateTypeArgument loc (TemplateArgName loc)
    | TemplateTemplateTypeArgument loc (TypeName loc) [TemplateTypeArgument loc]
    | PrimitiveTemplateTypeArgument loc (PrimitiveDatatype loc)
    | IntTemplateTypeArgument loc Integer
    | PublicTemplateTypeArgument loc
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (TemplateTypeArgument loc) where
    type LocOf (TemplateTypeArgument loc) = loc
    loc (GenericTemplateTypeArgument l _) = l
    loc (TemplateTemplateTypeArgument l _ _) = l
    loc (PrimitiveTemplateTypeArgument l _) = l
    loc (IntTemplateTypeArgument l _) = l
    loc (PublicTemplateTypeArgument l) = l

instance PP (TemplateTypeArgument loc) where
    pp (GenericTemplateTypeArgument _ targ) = pp targ
    pp (TemplateTemplateTypeArgument _ t args) = pp t <> abrackets (sepBy comma $ map pp args)
    pp (PrimitiveTemplateTypeArgument _ prim) = pp prim
    pp (IntTemplateTypeArgument _ i) = integer i
    pp (PublicTemplateTypeArgument _) = text "public"
  
data DimtypeSpecifier loc
    = DimSpecifier loc (Expression loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (DimtypeSpecifier loc) where
    type LocOf (DimtypeSpecifier loc) = loc
    loc (DimSpecifier l _) = l
  
instance PP (DimtypeSpecifier loc) where
    pp (DimSpecifier _ n) = brackets $ brackets $ pp n
  
-- Templates:                                                                  

data TemplateDeclaration loc
    = TemplateStructureDeclaration loc [TemplateQuantifier loc] (StructureDeclaration loc)
    | TemplateStructureSpecialization loc [TemplateQuantifier loc] [TemplateTypeArgument loc] (StructureDeclaration loc)
    | TemplateProcedureDeclaration loc [TemplateQuantifier loc] (ProcedureDeclaration loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (TemplateDeclaration loc) where
    type LocOf (TemplateDeclaration loc) = loc
    loc (TemplateStructureDeclaration l _ _) = l
    loc (TemplateStructureSpecialization l _ _ _) = l
    loc (TemplateProcedureDeclaration l _ _) = l
  
instance PP (TemplateDeclaration loc) where
    pp (TemplateStructureDeclaration _ qs struct) = text "template" <+> abrackets (sepBy comma (fmap pp qs)) <+> ppStruct Nothing struct
    pp (TemplateStructureSpecialization _ qs specials struct) = text "template" <+> abrackets (sepBy comma (fmap pp qs)) <+> ppStruct (Just specials) struct
    pp (TemplateProcedureDeclaration _ qs proc) = text "template" <+> abrackets (sepBy comma (fmap pp qs)) <+> pp proc
  
data TemplateQuantifier loc
    = DomainQuantifier loc (DomainName loc) (Maybe (KindName loc))
    | DimensionQuantifier loc (VarName loc)
    | DataQuantifier loc (TypeName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance Location loc => Located (TemplateQuantifier loc) where
    type LocOf (TemplateQuantifier loc) = loc
    loc (DomainQuantifier l _ _) = l
    loc (DimensionQuantifier l _) = l
    loc (DataQuantifier l _) = l

instance PP (TemplateQuantifier loc) where
    pp (DomainQuantifier _ d (Just k)) = text "domain" <+> pp d <+> char ':' <+> pp k
    pp (DomainQuantifier _ d Nothing) = text "domain" <+> pp d
    pp (DimensionQuantifier _ dim) = text "dimensionality" <+> pp dim
    pp (DataQuantifier _ t) = text "type" <+> pp t
  
 -- Structures:                                                                

data StructureDeclaration loc = StructureDeclaration loc (TypeName loc) [Attribute loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
 
structureDeclarationId :: StructureDeclaration loc -> Identifier
structureDeclarationId (StructureDeclaration _ tn _) = typeId tn
 
instance Location loc => Located (StructureDeclaration loc) where
    type LocOf (StructureDeclaration loc) = loc
    loc (StructureDeclaration l _ _) = l
  
instance PP (StructureDeclaration loc) where
    pp s = ppStruct Nothing s
  
ppStruct :: Maybe [TemplateTypeArgument loc] -> StructureDeclaration loc -> Doc
ppStruct Nothing (StructureDeclaration _ t as) = text "struct" <+> pp t <+> braces (vcat $ map pp as)
ppStruct (Just specials) (StructureDeclaration _ t as) = text "struct" <+> pp t <+> (sepBy comma (fmap pp specials)) <+> braces (vcat $ map pp as)
  
data Attribute loc = Attribute loc (TypeSpecifier loc) (AttributeName loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (Attribute loc) where
    type LocOf (Attribute loc) = loc
    loc (Attribute l _ _) = l
  
instance PP (Attribute loc) where
    pp (Attribute _ t v) = pp t <+> pp v <> char ';'

-- Procedures:

data ReturnTypeSpecifier loc = ReturnType loc (Maybe (TypeSpecifier loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
 
instance Location loc => Located (ReturnTypeSpecifier loc) where
    type LocOf (ReturnTypeSpecifier loc) = loc
    loc (ReturnType l _) = l
 
instance PP (ReturnTypeSpecifier loc) where
    pp (ReturnType loc Nothing) = text "void"
    pp (ReturnType loc (Just t)) = pp t
  
data ProcedureDeclaration loc
    = OperatorDeclaration loc (ReturnTypeSpecifier loc) (Op loc) [ProcedureParameter loc] [Statement loc]
    | ProcedureDeclaration loc (ReturnTypeSpecifier loc) (ProcedureName loc) [ProcedureParameter loc] [Statement loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (ProcedureDeclaration loc) where
    type LocOf (ProcedureDeclaration loc) = loc
    loc (OperatorDeclaration l _ _ _ _) = l
    loc (ProcedureDeclaration l _ _ _ _) = l
  
instance PP (ProcedureDeclaration loc) where
    pp (OperatorDeclaration _ ret op params stmts) = pp ret <+> text "operator" <+> pp op <+> parens (sepBy comma $ map pp params) <+> vcat (lbrace : map pp stmts ++ [rbrace])
    pp (ProcedureDeclaration _ ret proc params stmts) = pp ret <+> pp proc <+> parens (sepBy comma $ map pp params) <+> vcat (lbrace : map pp stmts ++ [rbrace])
  
data Op loc
    = OpAdd      loc
    | OpBand     loc
    | OpBor      loc
    | OpDiv      loc
    | OpGt       loc
    | OpLt       loc
    | OpMod      loc
    | OpMul      loc
    | OpSub      loc
    | OpXor      loc
    | OpEq       loc
    | OpGe       loc
    | OpLand     loc
    | OpLe       loc
    | OpLor      loc
    | OpNe       loc
    | OpShl      loc
    | OpShr      loc
    | OpExcM     loc
  deriving (Read,Show,Data,Typeable,Eq,Ord,Functor)

instance PP (Op loc) where
    pp (OpAdd  l) = text "+"
    pp (OpBand l) = text "&" 
    pp (OpBor  l) = text "|" 
    pp (OpDiv  l) = text "/" 
    pp (OpGt   l) = text ">" 
    pp (OpLt   l) = text "<" 
    pp (OpMod  l) = text "%" 
    pp (OpMul  l) = text "*" 
    pp (OpSub  l) = text "-" 
    pp (OpXor  l) = text "^" 
    pp (OpEq   l) = text "==" 
    pp (OpGe   l) = text ">=" 
    pp (OpLand l) = text "&&" 
    pp (OpLe   l) = text "<=" 
    pp (OpLor  l) = text "||" 
    pp (OpNe   l) = text "!=" 
    pp (OpShl  l) = text "<<" 
    pp (OpShr  l) = text ">>" 
    pp (OpExcM l) = text "!"
  
instance Location loc => Located (Op loc) where
    type LocOf (Op loc) = loc
    loc (OpAdd  l) = l
    loc (OpBand l) = l
    loc (OpBor  l) = l
    loc (OpDiv  l) = l
    loc (OpGt   l) = l
    loc (OpLt   l) = l
    loc (OpMod  l) = l
    loc (OpMul  l) = l
    loc (OpSub  l) = l
    loc (OpXor  l) = l
    loc (OpEq   l) = l 
    loc (OpGe   l) = l 
    loc (OpLand l) = l 
    loc (OpLe   l) = l 
    loc (OpLor  l) = l 
    loc (OpNe   l) = l 
    loc (OpShl  l) = l 
    loc (OpShr  l) = l 
    loc (OpExcM l) = l
  
-- Statements: 

data ForInitializer loc
    = InitializerExpression (Maybe (Expression loc))
    | InitializerVariable (VariableDeclaration loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

instance PP (ForInitializer loc) where
    pp (InitializerExpression e) = ppMb e
    pp (InitializerVariable v) = pp v

data Statement loc
    = CompoundStatement loc [Statement loc]
    | IfStatement loc (Expression loc) (Statement loc) (Maybe (Statement loc))
    | ForStatement loc (ForInitializer loc) (Maybe (Expression loc)) (Maybe (Expression loc)) (Statement loc)
    | WhileStatement loc (Expression loc) (Statement loc)
    | PrintStatement loc (NeList (Expression loc))
    | DowhileStatement loc (Statement loc) (Expression loc)
    | AssertStatement loc (Expression loc)
    | SyscallStatement loc String [SyscallParameter loc]
    | VarStatement loc (VariableDeclaration loc)
    | ReturnStatement loc (Maybe (Expression loc))
    | ContinueStatement loc
    | BreakStatement loc
    | ExpressionStatement loc (Expression loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
 
instance Location loc => Located (Statement loc) where
    type (LocOf (Statement loc)) = loc
    loc (CompoundStatement l _) = l
    loc (IfStatement l _ _ _) = l
    loc (ForStatement l _ _ _ _) = l
    loc (WhileStatement l _ _) = l
    loc (PrintStatement l _) = l
    loc (DowhileStatement l _ _) = l
    loc (AssertStatement l _) = l
    loc (SyscallStatement l _ _) = l
    loc (VarStatement l _) = l
    loc (ReturnStatement l _) = l
    loc (ContinueStatement l) = l
    loc (BreakStatement l) = l
    loc (ExpressionStatement l _) = l
 
instance PP [Statement loc] where
    pp [] = semi
    pp ss = vcat (lbrace : map pp ss ++ [rbrace])
 
instance PP (Statement loc) where
    pp (CompoundStatement _ ss) = pp ss
    pp (IfStatement _ e thenS elseS) = text "if" <+> parens (pp e) <+> pp thenS <+> ppElse elseS
        where
        ppElse Nothing = empty
        ppElse (Just s) = text "else" <+> pp s
    pp (ForStatement _ i e1 e2 s) = text "for" <> parens (pp i <> semi <> ppMb e1 <> semi <> ppMb e2) <+> pp s
    pp (WhileStatement _ e s) = text "while" <> parens (pp e) <+> pp s
    pp (PrintStatement _ es) = text "print" <> parens (sepBy comma $ fmap pp es) <> semi
    pp (DowhileStatement _ s e) = text "do" <+> pp s <+> text "while" <+> parens (pp e) <> semi
    pp (AssertStatement _ e) = text "assert" <> parens (pp e) <> semi
    pp (SyscallStatement _ n []) = text "__syscall" <> parens (text (show n)) <> semi
    pp (SyscallStatement _ n ps) = text "__syscall" <> parens (text (show n) <> comma <+> pp ps) <> semi
    pp (VarStatement _ vd) = pp vd <> semi
    pp (ReturnStatement _ e) = text "return" <+> ppMb e <> semi
    pp (ContinueStatement _) = text "continue" <> semi
    pp (BreakStatement _) = text "break" <> semi
    pp (ExpressionStatement _ e) = pp e <> semi
    
instance PP [SyscallParameter loc] where
    pp ps = sepBy comma $ map pp ps
 
data SyscallParameter loc
    = SyscallPush loc (Expression loc)
    | SyscallReturn loc (VarName loc)
    | SyscallPushRef loc (VarName loc)
    | SyscallPushCRef loc (Expression loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (SyscallParameter loc) where
    type LocOf (SyscallParameter loc) = loc
    loc (SyscallPush l _) = l
    loc (SyscallReturn l _) = l
    loc (SyscallPushRef l _) = l
    loc (SyscallPushCRef l _) = l
  
instance PP (SyscallParameter loc) where
    pp (SyscallPush _ e) = pp e
    pp (SyscallReturn _ v) = text "__return" <+> pp v
    pp (SyscallPushRef _ v) = text "__ref" <+> pp v
    pp (SyscallPushCRef _ e) = text "__cref" <+> pp e
  
-- Indices: not strictly expressions as they only appear in specific context

type Subscript loc = NeList (Index loc)

instance PP (Subscript loc) where
    pp is = brackets (sepBy comma $ fmap pp is)

data Index loc
    = IndexSlice loc (Maybe (Expression loc)) (Maybe (Expression loc))
    | IndexInt loc (Expression loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (Index loc) where
    type LocOf (Index loc) = loc
    loc (IndexSlice l _ _) = l
    loc (IndexInt l _) = l
  
instance PP (Index loc) where
    pp (IndexSlice _ e1 e2) = ppMb e1 <+> char ':' <+> ppMb e2
    pp (IndexInt _ e) = pp e
  
-- Expressions:  

data Expression loc
    = BinaryAssign loc (PostfixExpression loc) BinaryAssignOp (Expression loc)
    | QualExpr loc (Expression loc) (NeList (QualifiedType loc))
    | CondExpr loc (Expression loc) (Expression loc) (Expression loc)
    | BinaryExpr loc (Expression loc) (Op loc) (Expression loc)
    | PrimCastExpr loc (PrimitiveDatatype loc) (Expression loc)
    | VarCastExpr loc (TypeName loc) (Expression loc)
    | PrefixInc loc (PostfixExpression loc)
    | PrefixDec loc (PostfixExpression loc)
    | PostfixInc loc (PostfixExpression loc)
    | PostfixDec loc (PostfixExpression loc)
    | UminusExpr loc (Expression loc)
    | UnegExpr loc (Expression loc)
    | UinvExpr loc (Expression loc)
    | Upost loc (PostfixExpression loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (Expression loc) where
    type LocOf (Expression loc) = loc
    loc (BinaryAssign l _ _ _) = l
    loc (QualExpr l _ _) = l
    loc (CondExpr l _ _ _) = l
    loc (BinaryExpr l _ _ _) = l
    loc (PrimCastExpr l _ _) = l
    loc (VarCastExpr l _ _) = l
    loc (PrefixInc l _) = l
    loc (PrefixDec l _) = l
    loc (PostfixInc l _) = l
    loc (PostfixDec l _) = l
    loc (UminusExpr l _) = l
    loc (UnegExpr l _) = l
    loc (UinvExpr l _) = l
    loc (Upost l _) = l
  
instance PP (Expression loc) where
    pp (BinaryAssign _ post op e) = pp post <+> pp op <+> pp e
    pp (QualExpr _ e ts) = pp e <+> text "::" <+> sepBy space (fmap pp ts)
    pp (CondExpr _ lor thenE elseE) = pp lor <+> char '?' <+> pp thenE <+> char ':' <+> pp elseE
    pp (BinaryExpr _ e1 o e2) = parens (pp e1 <+> pp o <+> pp e2)
    pp (PrimCastExpr _ t e) = parens (pp t) <+> pp e
    pp (VarCastExpr _ t e) = parens (pp t) <+> pp e
    pp (PrefixInc _ e) = text "++" <+> pp e
    pp (PrefixDec _ e) = text "--" <+> pp e
    pp (PostfixInc _ e) = pp e <+> text "++"
    pp (PostfixDec _ e) = pp e <+> text "--"
    pp (UminusExpr _ e) = char '-' <+> pp e
    pp (UnegExpr _ e) = char '!' <+> pp e
    pp (UinvExpr _ e) = char '~' <+> pp e
    pp (Upost _ e) = pp e
  
data BinaryAssignOp
    = BinaryAssignEqual
    | BinaryAssignMul
    | BinaryAssignDiv
    | BinaryAssignMod 
    | BinaryAssignAdd
    | BinaryAssignSub
    | BinaryAssignAnd
    | BinaryAssignOr
    | BinaryAssignXor
  deriving (Read,Show,Data,Typeable,Eq,Ord)
  
instance PP BinaryAssignOp where
    pp BinaryAssignEqual = text "="
    pp BinaryAssignMul   = text "*="
    pp BinaryAssignDiv   = text "/="
    pp BinaryAssignMod   = text "%="
    pp BinaryAssignAdd   = text "+="
    pp BinaryAssignSub   = text "-="
    pp BinaryAssignAnd   = text "&="
    pp BinaryAssignOr    = text "|="
    pp BinaryAssignXor   = text "^="
  
data QualifiedType loc
    = PublicQualifiedType loc
    | PrimitiveQualifiedType loc (PrimitiveDatatype loc)
    | DimQualifiedType loc (DimtypeSpecifier loc)
    | GenericQualifiedType loc Identifier
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (QualifiedType loc) where
    type LocOf (QualifiedType loc) = loc
    loc (PublicQualifiedType l) = l
    loc (PrimitiveQualifiedType l _) = l
    loc (DimQualifiedType l _) = l
    loc (GenericQualifiedType l _) = l
  
instance PP (QualifiedType loc) where
    pp (PublicQualifiedType _) = text "public"
    pp (PrimitiveQualifiedType _ p) = pp p
    pp (DimQualifiedType _ dim) = pp dim
    pp (GenericQualifiedType _ iden) = pp iden
  
data CatExpression loc = CatExpr loc (Expression loc) (Expression loc) (Maybe Integer)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (CatExpression loc) where
    type (LocOf (CatExpression loc)) = loc
    loc (CatExpr l _ _ _) = l
  
instance PP (CatExpression loc) where
    pp (CatExpr _ e1 e2 (Just i)) = text "cat" <> parens (pp e1 <> comma <> pp e2 <> comma <> integer i)
    pp (CatExpr _ e1 e2 Nothing) = text "cat" <> parens (pp e1 <> comma <> pp e2)
  
data PostfixExpression loc
    = DeclassifyExpr loc (Expression loc)
    | SizeExpr loc (Expression loc)
    | ShapeExpr loc (Expression loc)
    | PostCatExpr loc (CatExpression loc)
    | DomainIdExpr loc (SecTypeSpecifier loc)
    | ReshapeExpr loc (NeList (Expression loc))
    | ToStringExpr loc (Expression loc)
    | StrlenExpr loc (Expression loc)
    | StringFromBytesExpr loc (Expression loc)
    | BytesFromStringExpr loc (Expression loc)
    | ProcCallExpr loc (ProcedureName loc) [Expression loc]
    | PostIndexExpr loc (PostfixExpression loc) (Subscript loc)
    | SelectionExpr loc (PostfixExpression loc) (AttributeName loc)
    | PostPrimExpr loc (PrimaryExpression loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (PostfixExpression loc) where
    type (LocOf (PostfixExpression loc)) = loc
    loc (DeclassifyExpr l _) = l
    loc (SizeExpr l _) = l
    loc (ShapeExpr l _) = l
    loc (PostCatExpr l _) = l
    loc (DomainIdExpr l _) = l
    loc (ReshapeExpr l _) = l
    loc (ToStringExpr l _) = l
    loc (StrlenExpr l _) = l
    loc (StringFromBytesExpr l _) = l
    loc (BytesFromStringExpr l _) = l
    loc (ProcCallExpr l _ _) = l
    loc (PostIndexExpr l _ _) = l
    loc (SelectionExpr l _ _) = l
    loc (PostPrimExpr l _) = l
  
instance PP (PostfixExpression loc) where
    pp (DeclassifyExpr _ e) = text "declassify" <> parens (pp e)
    pp (SizeExpr _ e) = text "size" <> parens (pp e)
    pp (ShapeExpr _ e) = text "shape" <> parens (pp e)
    pp (PostCatExpr _ e) = pp e
    pp (DomainIdExpr _ t) = text "__domainid" <> parens (pp t)
    pp (ReshapeExpr _ es) = text "reshape" <> parens (sepBy comma $ fmap pp es)
    pp (ToStringExpr _ e) = text "tostring" <> parens (pp e)
    pp (StrlenExpr _ e) = text "strlen" <> parens (pp e)
    pp (StringFromBytesExpr _ e) = text "__string_from_bytes" <> parens (pp e)
    pp (BytesFromStringExpr _ e) = text "__bytes_from_string" <> parens (pp e)
    pp (ProcCallExpr _ n es) = pp n <> parens (sepBy comma $ map pp es)
    pp (PostIndexExpr _ e s) = pp e <> pp s
    pp (SelectionExpr _ e v) = pp e <> char '.' <> pp v
    pp (PostPrimExpr _ e) = pp e
  
data PrimaryExpression loc
    = PExpr loc (Expression loc)
    | ArrayConstructorPExpr loc (NeList (Expression loc))
    | RVariablePExpr loc (VarName loc)
    | LitPExpr loc (Literal loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (PrimaryExpression loc) where
    type (LocOf (PrimaryExpression loc)) = loc
    loc (PExpr l _) = l
    loc (ArrayConstructorPExpr l _) = l
    loc (RVariablePExpr l _) = l
    loc (LitPExpr l _) = l
  
instance PP (PrimaryExpression loc) where
    pp (PExpr _ e) = parens (pp e)
    pp (ArrayConstructorPExpr _ es) = braces (sepBy comma $ fmap pp es)
    pp (RVariablePExpr _ v) = pp v
    pp (LitPExpr _ l) = pp l
  
data Literal loc
    = IntLit loc Integer
    | StringLit loc String
    | BoolLit loc Bool
    | FloatLit loc Double
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)
  
instance Location loc => Located (Literal loc) where
    type LocOf (Literal loc) = loc
    loc (IntLit l _) = l
    loc (StringLit l _) = l
    loc (BoolLit l _) = l
    loc (FloatLit l _) = l
  
instance PP (Literal loc) where
    pp (IntLit _ i) = integer i
    pp (StringLit _ s) = text (show s)
    pp (BoolLit _ b) = text (show b)
    pp (FloatLit _ f) = text (show f)


