{-# LANGUAGE DeriveGeneric, TemplateHaskell, TypeFamilies, DeriveFoldable, DeriveTraversable, DeriveFunctor, MultiParamTypeClasses, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances #-}

module Language.SecreC.Syntax where

import Data.Traversable
import Data.Foldable as Foldable
import Data.Generics hiding (empty,Generic)
import Data.Bifunctor.TH
import Data.Hashable

import Text.PrettyPrint as PP

import GHC.Generics (Generic)

import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Utils

-- Program and variable declarations:                                          

data Module iden loc = Module loc (Maybe (ModuleName iden loc)) (Program iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (Module iden loc)

moduleFile :: Location loc => Module iden loc -> String
moduleFile (Module l _ _) = posFileName $ locpos l

moduleId :: Module iden loc -> Maybe iden
moduleId (Module _ Nothing _) = Nothing
moduleId (Module _ (Just (ModuleName _ n)) _) = Just n

modulePosId :: Module Identifier Position -> Identifier
modulePosId = maybe "main" id . moduleId

addModuleImport :: ImportDeclaration iden loc -> Module iden loc -> Module iden loc
addModuleImport i (Module l n p) = Module l n (addProgramImport i p)

moduleImports :: Module iden loc -> [ImportDeclaration iden loc]
moduleImports (Module _ _ p) = programImports p

instance Location loc => Located (Module iden loc) where
    type LocOf (Module iden loc) = loc
    loc (Module l _ _) = l
    updLoc (Module _ x y) l = Module l x y

instance PP iden => PP (Module iden loc) where
    pp (Module _ (Just modulename) prog) = text "module" <+> pp modulename <+> text "where" $$ pp prog
    pp (Module _ Nothing prog) = pp prog

data AttributeName iden loc = AttributeName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (AttributeName iden loc)
  
attributeNameId :: AttributeName iden loc -> iden
attributeNameId (AttributeName _ i) = i
  
instance Location loc => Located (AttributeName iden loc) where
    type LocOf (AttributeName iden loc) = loc
    loc (AttributeName l _) = l
    updLoc (AttributeName _ x) l = AttributeName l x
  
instance PP iden => PP (AttributeName iden loc) where
    pp (AttributeName _ iden) = pp iden

data ModuleName iden loc = ModuleName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (ModuleName iden loc)
  
instance Location loc => Located (ModuleName iden loc) where
    type LocOf (ModuleName iden loc) = loc
    loc (ModuleName l _) = l
    updLoc (ModuleName _ x) l = ModuleName l x
  
instance PP iden => PP (ModuleName iden loc) where
    pp (ModuleName _ iden) = pp iden

data TemplateArgName iden loc = TemplateArgName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (TemplateArgName iden loc)
  
instance Location loc => Located (TemplateArgName iden loc) where
    type LocOf (TemplateArgName iden loc) = loc
    loc (TemplateArgName l _) = l
    updLoc (TemplateArgName _ x) l = TemplateArgName l x
  
instance PP iden => PP (TemplateArgName iden loc) where
    pp (TemplateArgName _ iden) = pp iden

data Program iden loc = Program loc [ImportDeclaration iden loc] [GlobalDeclaration iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (Program iden loc)

addProgramImport :: ImportDeclaration iden loc -> Program iden loc -> Program iden loc
addProgramImport i (Program l is gs) = Program l (i:is) gs

programImports :: Program iden loc -> [ImportDeclaration iden loc]
programImports (Program _ is _) = is
  
instance Location loc => Located (Program iden loc) where
    type LocOf (Program iden loc) = loc
    loc (Program l _ _) = l
    updLoc (Program _ x y) l = Program l x y
  
instance PP iden => PP (Program iden loc) where
    pp (Program _ is gs) = pp is $$ pp gs

instance PP iden => PP [ImportDeclaration iden loc] where
    pp is = vcat $ map pp is

instance PP iden => PP [GlobalDeclaration iden loc] where
    pp gs = vcat $ map pp gs

data ImportDeclaration iden loc = Import loc (ModuleName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (ImportDeclaration iden loc)
  
instance Location loc => Located (ImportDeclaration iden loc) where
    type LocOf (ImportDeclaration iden loc) = loc
    loc (Import l _) = l
    updLoc (Import _ x) l = Import l x
 
instance PP iden => PP (ImportDeclaration iden loc) where
    pp (Import _ modulename) = text "import" <+> pp modulename

data GlobalDeclaration iden loc
    = GlobalVariable loc (VariableDeclaration iden loc)
    | GlobalConst loc (ConstDeclaration iden loc)
    | GlobalDomain loc (DomainDeclaration iden loc)
    | GlobalKind loc (KindDeclaration iden loc)
    | GlobalProcedure loc (ProcedureDeclaration iden loc)
    | GlobalStructure loc (StructureDeclaration iden loc)
    | GlobalTemplate loc (TemplateDeclaration iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (GlobalDeclaration iden loc)

instance Location loc => Located (GlobalDeclaration iden loc) where
    type LocOf (GlobalDeclaration iden loc) = loc
    loc (GlobalVariable l vd) = l
    loc (GlobalConst l vd) = l
    loc (GlobalDomain l dd) = l
    loc (GlobalKind l kd) = l
    loc (GlobalProcedure l pd) = l
    loc (GlobalStructure l sd) = l
    loc (GlobalTemplate l td) = l
    updLoc (GlobalVariable _ vd) l = GlobalVariable l vd
    updLoc (GlobalConst _ vd) l = GlobalConst l vd
    updLoc (GlobalDomain _ dd) l = GlobalDomain l dd
    updLoc (GlobalKind _ kd) l = GlobalKind l kd
    updLoc (GlobalProcedure _ pd) l = GlobalProcedure l pd
    updLoc (GlobalStructure _ sd) l = GlobalStructure l sd
    updLoc (GlobalTemplate _ td) l = GlobalTemplate l td

instance PP iden => PP (GlobalDeclaration iden loc) where
    pp (GlobalVariable _ vd) = pp vd
    pp (GlobalConst _ vd) = pp vd
    pp (GlobalDomain _ dd) = pp dd
    pp (GlobalKind _ kd) = pp kd
    pp (GlobalProcedure _ pd) = pp pd
    pp (GlobalStructure _ sd) = pp sd
    pp (GlobalTemplate _ td) = pp td

data KindDeclaration iden loc = Kind loc (KindName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (KindDeclaration iden loc)
 
instance Location loc => Located (KindDeclaration iden loc) where
    type LocOf (KindDeclaration iden loc) = loc
    loc (Kind l _) = l
    updLoc (Kind _ x) l = Kind l x
 
instance PP iden => PP (KindDeclaration iden loc) where
    pp (Kind _ kname) = text "kind" <+> pp kname
  
data KindName iden loc = KindName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (KindName iden loc)

kindId :: KindName iden loc -> iden
kindId (KindName _ n) = n

instance Location loc => Located (KindName iden loc) where
    type LocOf (KindName iden loc) = loc
    loc (KindName l _) = l
    updLoc (KindName _ x) l = KindName l x

instance PP iden => PP (KindName iden loc) where
    pp (KindName _ iden) = pp iden

data DomainDeclaration iden loc = Domain loc (DomainName iden loc) (KindName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (DomainDeclaration iden loc)

instance Location loc => Located (DomainDeclaration iden loc) where
    type LocOf (DomainDeclaration iden loc) = loc
    loc (Domain l _ _) = l
    updLoc (Domain _ x y) l = Domain l x y

instance PP iden => PP (DomainDeclaration iden loc) where
    pp (Domain _ dom kind) = text "domain" <+> pp dom <+> pp kind
 
data DomainName iden loc = DomainName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (DomainName iden loc)

instance Location loc => Located (DomainName iden loc) where
    type LocOf (DomainName iden loc) = loc
    loc (DomainName l _) = l
    updLoc (DomainName _ x) l = DomainName l x

instance PP iden => PP (DomainName iden loc) where
    pp (DomainName _ iden) = pp iden

data ProcedureName iden loc = ProcedureName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (ProcedureName iden loc)
  
instance Location loc => Located (ProcedureName iden loc) where
    type LocOf (ProcedureName iden loc) = loc
    loc (ProcedureName l _) = l
    updLoc (ProcedureName _ x) l = ProcedureName l x
 
instance PP iden => PP (ProcedureName iden loc) where
    pp (ProcedureName _ iden) = pp iden

data VarName iden loc = VarName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (VarName iden loc)

varNameId :: VarName iden loc -> iden
varNameId (VarName _ i) = i
  
instance Location loc => Located (VarName iden loc) where
    type LocOf (VarName iden loc) = loc
    loc (VarName l _) = l
    updLoc (VarName _ x) l = VarName l x
 
instance PP iden => PP (VarName iden loc) where
    pp (VarName _ iden) = pp iden

data TypeName iden loc = TypeName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (TypeName iden loc)

typeId :: TypeName iden loc -> iden
typeId (TypeName _ i) = i

instance Location loc => Located (TypeName iden loc) where
    type LocOf (TypeName iden loc) = loc
    loc (TypeName l _) = l
    updLoc (TypeName _ x) l = TypeName l x

instance PP iden => PP (TypeName iden loc) where
    pp (TypeName _ iden) = pp iden

type Identifier = String

instance PP String where
    pp s = text s

data ConstInitialization iden loc = ConstInitialization loc (VarName iden loc) (Maybe (Sizes iden loc)) (Maybe (Expression iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (ConstInitialization iden loc)
  
instance Location loc => Located (ConstInitialization iden loc) where
    type LocOf (ConstInitialization iden loc) = loc
    loc (ConstInitialization l _ _ _) = l
    updLoc (ConstInitialization _ x y z) l = ConstInitialization l x y z
 
instance PP iden => PP (ConstInitialization iden loc) where
    pp (ConstInitialization _ v dim ex) = pp v <+> ppDim dim <+> ppExp ex
        where
        ppDim Nothing = empty
        ppDim (Just dim) = parens (pp dim)
        ppExp Nothing = empty
        ppExp (Just e) = text "=" <+> pp e

data VariableInitialization iden loc = VariableInitialization loc (VarName iden loc) (Maybe (Sizes iden loc)) (Maybe (Expression iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (VariableInitialization iden loc)
  
instance Location loc => Located (VariableInitialization iden loc) where
    type LocOf (VariableInitialization iden loc) = loc
    loc (VariableInitialization l _ _ _) = l
    updLoc (VariableInitialization _ x y z) l = VariableInitialization l x y z
 
instance PP iden => PP (VariableInitialization iden loc) where
    pp (VariableInitialization _ v dim ex) = pp v <+> ppDim dim <+> ppExp ex
        where
        ppDim Nothing = empty
        ppDim (Just dim) = parens (pp dim)
        ppExp Nothing = empty
        ppExp (Just e) = text "=" <+> pp e

newtype Sizes iden loc = Sizes (NeList (Expression iden loc,IsVariadic))
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (Sizes iden loc)
  
unSizes (Sizes xs) = xs
sizesList = Foldable.toList . unSizes

instance Functor (Sizes iden) where
    fmap f (Sizes xs) = Sizes $ fmap (\(x,y) -> (fmap f x,y)) xs

instance Location loc => Located (Sizes iden loc) where
    type LocOf (Sizes iden loc) = loc
    loc (Sizes xs) = loc (fst $ headNe xs)
    updLoc (Sizes xs) l = Sizes (updHeadNe (\(x,y) -> (updLoc x l,y)) xs)

instance PP iden => PP (Sizes iden loc) where
    pp (Sizes es) = parens (sepBy comma $ fmap (ppVariadicArg pp) es)

data ConstDeclaration iden loc = ConstDeclaration loc (TypeSpecifier iden loc) (NeList (ConstInitialization iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (ConstDeclaration iden loc)

instance Location loc => Located (ConstDeclaration iden loc) where
    type LocOf (ConstDeclaration iden loc) = loc
    loc (ConstDeclaration l _ _) = l
    updLoc (ConstDeclaration _ x y) l = ConstDeclaration l x y

instance PP iden => PP (ConstDeclaration iden loc) where
    pp (ConstDeclaration _ t is) = pp t <+> sepBy comma (fmap pp is)

data VariableDeclaration iden loc = VariableDeclaration loc (TypeSpecifier iden loc) (NeList (VariableInitialization iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (VariableDeclaration iden loc)

instance Location loc => Located (VariableDeclaration iden loc) where
    type LocOf (VariableDeclaration iden loc) = loc
    loc (VariableDeclaration l _ _) = l
    updLoc (VariableDeclaration _ x y) l = VariableDeclaration l x y

instance PP iden => PP (VariableDeclaration iden loc) where
    pp (VariableDeclaration _ t is) = pp t <+> sepBy comma (fmap pp is)

type IsVariadic = Bool

data ProcedureParameter iden loc
    = ProcedureParameter loc (TypeSpecifier iden loc) IsVariadic (VarName iden loc) (Maybe (Sizes iden loc))
    | ConstProcedureParameter loc (TypeSpecifier iden loc) IsVariadic (VarName iden loc) (Maybe (Sizes iden loc)) (Maybe (Expression iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (ProcedureParameter iden loc)

instance Location loc => Located (ProcedureParameter iden loc) where
    type LocOf (ProcedureParameter iden loc) = loc
    loc (ProcedureParameter l _ _ _ _) = l
    loc (ConstProcedureParameter l _ _ _ _ _) = l
    updLoc (ProcedureParameter _ b x y z) l = ProcedureParameter l b x y z
    updLoc (ConstProcedureParameter _ b x y z w) l = ConstProcedureParameter l b x y z w

instance PP iden => PP (ProcedureParameter iden loc) where
    pp (ProcedureParameter _ t b v sz) = pp t <> ppVariadic b <+> pp v <> parens (pp sz)
    pp (ConstProcedureParameter _ t b v sz e) = text "const" <+> pp t <> ppVariadic b <+> pp v <> parens (pp sz) <+> ppOpt e (braces . pp)

-- Types:                                                                      

data TypeSpecifier iden loc = TypeSpecifier loc (Maybe (SecTypeSpecifier iden loc)) (DatatypeSpecifier iden loc) (Maybe (DimtypeSpecifier iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (TypeSpecifier iden loc)
  
typeSpecifierLoc :: TypeSpecifier iden loc -> loc
typeSpecifierLoc (TypeSpecifier l _ _ _) = l

instance Location loc => Located (TypeSpecifier iden loc) where
    type LocOf (TypeSpecifier iden loc) = loc
    loc (TypeSpecifier l _ _ _) = l
    updLoc (TypeSpecifier _ x y z) l = TypeSpecifier l x y z
  
instance PP iden => PP (TypeSpecifier iden loc) where
    pp (TypeSpecifier _ sec t dim) = ppMb sec <+> pp t <+> ppMb dim

data SecTypeSpecifier iden loc
    = PublicSpecifier loc
    | PrivateSpecifier loc (DomainName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (SecTypeSpecifier iden loc)

instance Location loc => Located (SecTypeSpecifier iden loc) where
    type LocOf (SecTypeSpecifier iden loc) = loc
    loc (PublicSpecifier l) = l
    loc (PrivateSpecifier l _) = l
    updLoc (PublicSpecifier _) l = PublicSpecifier l
    updLoc (PrivateSpecifier _ x) l = PrivateSpecifier l x

instance PP iden => PP (SecTypeSpecifier iden loc) where
    pp (PublicSpecifier _) = text "public"
    pp (PrivateSpecifier _ n) = pp n

data DatatypeSpecifier iden loc
    = PrimitiveSpecifier loc (PrimitiveDatatype loc)
    | TemplateSpecifier loc (TypeName iden loc) [(TemplateTypeArgument iden loc,IsVariadic)]
    | VariableSpecifier loc (TypeName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (DatatypeSpecifier iden loc)

instance Location loc => Located (DatatypeSpecifier iden loc) where
    type LocOf (DatatypeSpecifier iden loc) = loc
    loc (PrimitiveSpecifier l _) = l
    loc (TemplateSpecifier l _ _) = l
    loc (VariableSpecifier l _) = l
    updLoc (PrimitiveSpecifier _ x) l = PrimitiveSpecifier l x
    updLoc (TemplateSpecifier _ x y) l = TemplateSpecifier l x y
    updLoc (VariableSpecifier _ x) l = VariableSpecifier l x

instance PP iden => PP (DatatypeSpecifier iden loc) where
    pp (PrimitiveSpecifier _ prim) = pp prim
    pp (TemplateSpecifier _ t args) = pp t <> abrackets (sepBy comma $ map (ppVariadicArg pp) args)
    pp (VariableSpecifier _ tn) = pp tn

data PrimitiveDatatype loc
    = DatatypeBool       loc
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
    | DatatypeFloat32    loc
    | DatatypeFloat64    loc
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance Hashable loc => Hashable (PrimitiveDatatype loc)

isPrimInt :: PrimitiveDatatype loc -> Bool
isPrimInt (DatatypeInt8       loc) = True
isPrimInt (DatatypeInt16      loc) = True
isPrimInt (DatatypeInt32      loc) = True
isPrimInt (DatatypeInt64      loc) = True
isPrimInt _ = False

isPrimUint :: PrimitiveDatatype loc -> Bool
isPrimUint (DatatypeUint8      loc) = True
isPrimUint (DatatypeUint16     loc) = True
isPrimUint (DatatypeUint32     loc) = True
isPrimUint (DatatypeUint64     loc) = True
isPrimUint (DatatypeXorUint8   loc) = True
isPrimUint (DatatypeXorUint16  loc) = True
isPrimUint (DatatypeXorUint32  loc) = True
isPrimUint (DatatypeXorUint64  loc) = True
isPrimUint _ = False

isPrimFloat :: PrimitiveDatatype loc -> Bool
isPrimFloat (DatatypeFloat32    loc) = True
isPrimFloat (DatatypeFloat64    loc) = True
isPrimFloat _ = False

isPrimNumeric :: PrimitiveDatatype loc -> Bool
isPrimNumeric x = isPrimInt x || isPrimUint x || isPrimFloat x

instance Location loc => Located (PrimitiveDatatype loc) where
    type LocOf (PrimitiveDatatype loc) = loc
    loc (DatatypeBool       l) = l
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
    loc (DatatypeFloat32    l) = l
    loc (DatatypeFloat64    l) = l
    updLoc (DatatypeBool       _) l = DatatypeBool      l
    updLoc (DatatypeInt8       _) l = DatatypeInt8      l
    updLoc (DatatypeUint8      _) l = DatatypeUint8     l
    updLoc (DatatypeInt16      _) l = DatatypeInt16     l
    updLoc (DatatypeUint16     _) l = DatatypeUint16    l
    updLoc (DatatypeInt32      _) l = DatatypeInt32     l
    updLoc (DatatypeUint32     _) l = DatatypeUint32    l
    updLoc (DatatypeInt64      _) l = DatatypeInt64     l
    updLoc (DatatypeUint64     _) l = DatatypeUint64    l
    updLoc (DatatypeString     _) l = DatatypeString    l
    updLoc (DatatypeXorUint8   _) l = DatatypeXorUint8  l
    updLoc (DatatypeXorUint16  _) l = DatatypeXorUint16 l
    updLoc (DatatypeXorUint32  _) l = DatatypeXorUint32 l
    updLoc (DatatypeXorUint64  _) l = DatatypeXorUint64 l
    updLoc (DatatypeFloat32    _) l = DatatypeFloat32   l
    updLoc (DatatypeFloat64    _) l = DatatypeFloat64   l

instance PP (PrimitiveDatatype loc) where
    pp (DatatypeBool       _) = text "bool"
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
    pp (DatatypeFloat32    _) = text "float32"
    pp (DatatypeFloat64    _) = text "float64"
  
data TemplateTypeArgument iden loc
    = GenericTemplateTypeArgument loc (TemplateArgName iden loc)
    | TemplateTemplateTypeArgument loc (TypeName iden loc) [(TemplateTypeArgument iden loc,IsVariadic)]
    | PrimitiveTemplateTypeArgument loc (PrimitiveDatatype loc)
    | ExprTemplateTypeArgument loc (Expression iden loc)
    | PublicTemplateTypeArgument loc
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (TemplateTypeArgument iden loc)

instance Location loc => Located (TemplateTypeArgument iden loc) where
    type LocOf (TemplateTypeArgument iden loc) = loc
    loc (GenericTemplateTypeArgument l _) = l
    loc (TemplateTemplateTypeArgument l _ _) = l
    loc (PrimitiveTemplateTypeArgument l _) = l
    loc (ExprTemplateTypeArgument l _) = l
    loc (PublicTemplateTypeArgument l) = l
    updLoc (GenericTemplateTypeArgument _ x) l = GenericTemplateTypeArgument l x
    updLoc (TemplateTemplateTypeArgument _ x y) l = TemplateTemplateTypeArgument l x y
    updLoc (PrimitiveTemplateTypeArgument _ x) l = PrimitiveTemplateTypeArgument l x
    updLoc (ExprTemplateTypeArgument _ x) l = ExprTemplateTypeArgument l x
    updLoc (PublicTemplateTypeArgument _) l = PublicTemplateTypeArgument l

instance PP iden => PP (TemplateTypeArgument iden loc) where
    pp (GenericTemplateTypeArgument _ targ) = pp targ
    pp (TemplateTemplateTypeArgument _ t args) = pp t <> abrackets (sepBy comma $ map (ppVariadicArg pp) args)
    pp (PrimitiveTemplateTypeArgument _ prim) = pp prim
    pp (ExprTemplateTypeArgument _ e) = pp e
    pp (PublicTemplateTypeArgument _) = text "public"
  
data DimtypeSpecifier iden loc
    = DimSpecifier loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (DimtypeSpecifier iden loc)
  
instance Location loc => Located (DimtypeSpecifier iden loc) where
    type LocOf (DimtypeSpecifier iden loc) = loc
    loc (DimSpecifier l _) = l
    updLoc (DimSpecifier _ x) l = DimSpecifier l x
  
instance PP iden => PP (DimtypeSpecifier iden loc) where
    pp (DimSpecifier _ n) = brackets $ brackets $ pp n
  
-- Templates:                                                                  

data TemplateDeclaration iden loc
    = TemplateStructureDeclaration loc [TemplateQuantifier iden loc] (StructureDeclaration iden loc)
    | TemplateStructureSpecialization loc [TemplateQuantifier iden loc] [(TemplateTypeArgument iden loc,IsVariadic)] (StructureDeclaration iden loc)
    | TemplateProcedureDeclaration loc [TemplateQuantifier iden loc] (ProcedureDeclaration iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (TemplateDeclaration iden loc)
  
instance Location loc => Located (TemplateDeclaration iden loc) where
    type LocOf (TemplateDeclaration iden loc) = loc
    loc (TemplateStructureDeclaration l _ _) = l
    loc (TemplateStructureSpecialization l _ _ _) = l
    loc (TemplateProcedureDeclaration l _ _) = l
    updLoc (TemplateStructureDeclaration _ x y) l = TemplateStructureDeclaration l x y
    updLoc (TemplateStructureSpecialization _ x y z) l = TemplateStructureSpecialization l x y z
    updLoc (TemplateProcedureDeclaration _ x y) l = TemplateProcedureDeclaration l x y
  
instance PP iden => PP (TemplateDeclaration iden loc) where
    pp (TemplateStructureDeclaration _ qs struct) = text "template" <+> abrackets (sepBy comma (fmap pp qs)) <+> ppStruct Nothing struct
    pp (TemplateStructureSpecialization _ qs specials struct) = text "template" <+> abrackets (sepBy comma (fmap pp qs)) <+> ppStruct (Just specials) struct
    pp (TemplateProcedureDeclaration _ qs proc) = text "template" <+> abrackets (sepBy comma (fmap pp qs)) <+> pp proc
  
data TemplateQuantifier iden loc
    = DomainQuantifier loc IsVariadic (DomainName iden loc) (Maybe (KindName iden loc))
    | DimensionQuantifier loc IsVariadic (VarName iden loc) (Maybe (Expression iden loc))
    | DataQuantifier loc IsVariadic (TypeName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (TemplateQuantifier iden loc)

instance Location loc => Located (TemplateQuantifier iden loc) where
    type LocOf (TemplateQuantifier iden loc) = loc
    loc (DomainQuantifier l _ _ _) = l
    loc (DimensionQuantifier l _ _ _) = l
    loc (DataQuantifier l _ _) = l
    updLoc (DomainQuantifier _ b x y) l = DomainQuantifier l b x y
    updLoc (DimensionQuantifier _ b x y) l = DimensionQuantifier l b x y
    updLoc (DataQuantifier _ b x) l = DataQuantifier l b x

ppVariadic b = if b then text "..." else PP.empty

instance PP iden => PP (TemplateQuantifier iden loc) where
    pp (DomainQuantifier _ b d (Just k)) = text "domain" <> ppVariadic b <+> pp d <+> char ':' <+> pp k
    pp (DomainQuantifier _ b d Nothing) = text "domain" <> ppVariadic b <+> pp d
    pp (DimensionQuantifier _ b dim e) = text "dim" <> ppVariadic b <+> pp dim <+> ppOpt e (braces . pp)
    pp (DataQuantifier _ b t) = text "type" <> ppVariadic b <+> pp t
  
 -- Structures:                                                                

data StructureDeclaration iden loc = StructureDeclaration loc (TypeName iden loc) [Attribute iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (StructureDeclaration iden loc)

structureDeclarationId :: StructureDeclaration iden loc -> iden
structureDeclarationId (StructureDeclaration _ tn _) = typeId tn
 
instance Location loc => Located (StructureDeclaration iden loc) where
    type LocOf (StructureDeclaration iden loc) = loc
    loc (StructureDeclaration l _ _) = l
    updLoc (StructureDeclaration _ x y) l = StructureDeclaration l x y
  
instance PP iden => PP (StructureDeclaration iden loc) where
    pp s = ppStruct Nothing s
  
ppStruct :: PP iden => Maybe [(TemplateTypeArgument iden loc,IsVariadic)] -> StructureDeclaration iden loc -> Doc
ppStruct Nothing (StructureDeclaration _ t as) = text "struct" <+> pp t <+> braces (vcat $ map pp as)
ppStruct (Just specials) (StructureDeclaration _ t as) = text "struct" <+> pp t <+> abrackets (sepBy comma (fmap (ppVariadicArg pp) specials)) <+> braces (vcat $ map pp as)
  
data Attribute iden loc = Attribute loc (TypeSpecifier iden loc) (AttributeName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (Attribute iden loc)
 
instance Location loc => Located (Attribute iden loc) where
    type LocOf (Attribute iden loc) = loc
    loc (Attribute l _ _) = l
    updLoc (Attribute _ x y) l = Attribute l x y
  
instance PP iden => PP (Attribute iden loc) where
    pp (Attribute _ t v) = pp t <+> pp v <> char ';'

-- Procedures:

type SizedTypeSpecifier iden loc = (TypeSpecifier iden loc,Maybe (Sizes iden loc))

ppSizedTypeSpecifier (x,Nothing) = pp x
ppSizedTypeSpecifier (x,Just s) = pp x <> parens (pp s)

data ReturnTypeSpecifier iden loc = ReturnType loc (Maybe (SizedTypeSpecifier iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (ReturnTypeSpecifier iden loc)

instance Location loc => Located (ReturnTypeSpecifier iden loc) where
    type LocOf (ReturnTypeSpecifier iden loc) = loc
    loc (ReturnType l _) = l
    updLoc (ReturnType _ x) l = ReturnType l x
 
instance PP iden => PP (ReturnTypeSpecifier iden loc) where
    pp (ReturnType loc Nothing) = text "void"
    pp (ReturnType loc (Just (t,sz))) = pp t <> parens (pp sz)
  
ppConst isConst = if isConst then text "const" else PP.empty
  
data ProcedureDeclaration iden loc
    = OperatorDeclaration loc
        (ReturnTypeSpecifier iden loc)
        (Op iden loc)
        [ProcedureParameter iden loc]
        [Statement iden loc]
    | ProcedureDeclaration loc
        (ReturnTypeSpecifier iden loc)
        (ProcedureName iden loc)
        [ProcedureParameter iden loc]
        [Statement iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (ProcedureDeclaration iden loc)

instance Location loc => Located (ProcedureDeclaration iden loc) where
    type LocOf (ProcedureDeclaration iden loc) = loc
    loc (OperatorDeclaration l _ _ _ _) = l
    loc (ProcedureDeclaration l _ _ _ _) = l
    updLoc (OperatorDeclaration _ x y z w) l = OperatorDeclaration l x y z w
    updLoc (ProcedureDeclaration _ x y z w) l = ProcedureDeclaration l x y z w
  
instance PP iden => PP (ProcedureDeclaration iden loc) where
    pp (OperatorDeclaration _ ret op params stmts) = pp ret <+> text "operator" <+> pp op <+> parens (sepBy comma $ map pp params) <+> vcat (lbrace : map pp stmts ++ [rbrace])
    pp (ProcedureDeclaration _ ret proc params stmts) = pp ret <+> pp proc <+> parens (sepBy comma $ map pp params) <+> vcat (lbrace : map pp stmts ++ [rbrace])
  
data Op iden loc
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
    | OpNot      loc
    | OpCast     loc (CastType iden loc)
    | OpInv      loc
  deriving (Read,Show,Data,Typeable,Eq,Ord,Functor,Generic)

instance (Hashable iden,Hashable loc) => Hashable (Op iden loc)

isBoolOp :: Op iden loc -> Bool
isBoolOp (OpLor _) = True
isBoolOp (OpNot _) = True
isBoolOp (OpXor _) = True
isBoolOp (OpLand _) = True
isBoolOp _ = False

isCmpOp :: Op iden loc -> Bool
isCmpOp (OpEq _) = True
isCmpOp (OpNe _) = True
isCmpOp (OpLt _) = True
isCmpOp (OpLe _) = True
isCmpOp (OpGt _) = True
isCmpOp (OpGe _) = True
isCmpOp _ = False

isOpCast :: Op iden loc -> Maybe (CastType iden loc)
isOpCast (OpCast _ t) = Just t
isOpCast _ = Nothing

instance PP iden => PP (Op iden loc) where
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
    pp (OpNot l) = text "!"
    pp (OpCast l t) = parens (pp t)
    pp (OpInv l) = text "~"
  
instance Location loc => Located (Op iden loc) where
    type LocOf (Op iden loc) = loc
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
    loc (OpNot l)  = l
    loc (OpCast l t) = l
    loc (OpInv l)  = l
    updLoc (OpAdd  _) l = OpAdd  l
    updLoc (OpBand _) l = OpBand l
    updLoc (OpBor  _) l = OpBor  l
    updLoc (OpDiv  _) l = OpDiv  l
    updLoc (OpGt   _) l = OpGt   l
    updLoc (OpLt   _) l = OpLt   l
    updLoc (OpMod  _) l = OpMod  l
    updLoc (OpMul  _) l = OpMul  l
    updLoc (OpSub  _) l = OpSub  l
    updLoc (OpXor  _) l = OpXor  l
    updLoc (OpEq   _) l = OpEq   l
    updLoc (OpGe   _) l = OpGe   l
    updLoc (OpLand _) l = OpLand l
    updLoc (OpLe   _) l = OpLe   l
    updLoc (OpLor  _) l = OpLor  l
    updLoc (OpNe   _) l = OpNe   l
    updLoc (OpShl  _) l = OpShl  l
    updLoc (OpShr  _) l = OpShr  l
    updLoc (OpNot  _) l = OpNot  l
    updLoc (OpCast _ t) l = OpCast l t
    updLoc (OpInv  _) l = OpInv  l
  
-- Statements: 

data ForInitializer iden loc
    = InitializerExpression (Maybe (Expression iden loc))
    | InitializerVariable (VariableDeclaration iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (ForInitializer iden loc)
 
instance PP iden => PP (ForInitializer iden loc) where
    pp (InitializerExpression e) = ppMb e
    pp (InitializerVariable v) = pp v

data Statement iden loc
    = CompoundStatement loc [Statement iden loc]
    | IfStatement loc (Expression iden loc) (Statement iden loc) (Maybe (Statement iden loc))
    | ForStatement loc (ForInitializer iden loc) (Maybe (Expression iden loc)) (Maybe (Expression iden loc)) (Statement iden loc)
    | WhileStatement loc (Expression iden loc) (Statement iden loc)
    | PrintStatement loc [(Expression iden loc,IsVariadic)]
    | DowhileStatement loc (Statement iden loc) (Expression iden loc)
    | AssertStatement loc (Expression iden loc)
    | SyscallStatement loc String [SyscallParameter iden loc]
    | ConstStatement loc (ConstDeclaration iden loc)
    | VarStatement loc (VariableDeclaration iden loc)
    | ReturnStatement loc (Maybe (Expression iden loc))
    | ContinueStatement loc
    | BreakStatement loc
    | ExpressionStatement loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (Statement iden loc)

instance Location loc => Located (Statement iden loc) where
    type (LocOf (Statement iden loc)) = loc
    loc (CompoundStatement l _) = l
    loc (IfStatement l _ _ _) = l
    loc (ForStatement l _ _ _ _) = l
    loc (WhileStatement l _ _) = l
    loc (PrintStatement l _) = l
    loc (DowhileStatement l _ _) = l
    loc (AssertStatement l _) = l
    loc (SyscallStatement l _ _) = l
    loc (VarStatement l _) = l
    loc (ConstStatement l _) = l
    loc (ReturnStatement l _) = l
    loc (ContinueStatement l) = l
    loc (BreakStatement l) = l
    loc (ExpressionStatement l _) = l
    updLoc (CompoundStatement _ x) l = CompoundStatement l x
    updLoc (IfStatement _ x y z) l = IfStatement l x y z
    updLoc (ForStatement _ x y z w) l = ForStatement l x y z w
    updLoc (WhileStatement _ x y) l = WhileStatement l x y
    updLoc (PrintStatement _ x) l = PrintStatement l x
    updLoc (DowhileStatement _ x y) l = DowhileStatement l x y
    updLoc (AssertStatement _ x) l = AssertStatement l x
    updLoc (SyscallStatement _ x y) l = SyscallStatement l x y
    updLoc (VarStatement _ x) l = VarStatement l x
    updLoc (ConstStatement _ x) l = ConstStatement l x
    updLoc (ReturnStatement _ x) l = ReturnStatement l x
    updLoc (ContinueStatement _) l = ContinueStatement l
    updLoc (BreakStatement _) l = BreakStatement l
    updLoc (ExpressionStatement _ x) l = ExpressionStatement l x
 
instance PP iden => PP [Statement iden loc] where
    pp [] = semi
    pp ss = vcat (lbrace : map pp ss ++ [rbrace])
 
instance PP iden => PP (Statement iden loc) where
    pp (CompoundStatement _ ss) = pp ss
    pp (IfStatement _ e thenS elseS) = text "if" <+> parens (pp e) <+> pp thenS <+> ppElse elseS
        where
        ppElse Nothing = empty
        ppElse (Just s) = text "else" <+> pp s
    pp (ForStatement _ i e1 e2 s) = text "for" <> parens (pp i <> semi <> ppMb e1 <> semi <> ppMb e2) <+> pp s
    pp (WhileStatement _ e s) = text "while" <> parens (pp e) <+> pp s
    pp (PrintStatement _ es) = text "print" <> parens (pp es) <> semi
    pp (DowhileStatement _ s e) = text "do" <+> pp s <+> text "while" <+> parens (pp e) <> semi
    pp (AssertStatement _ e) = text "assert" <> parens (pp e) <> semi
    pp (SyscallStatement _ n []) = text "__syscall" <> parens (text (show n)) <> semi
    pp (SyscallStatement _ n ps) = text "__syscall" <> parens (text (show n) <> comma <+> ppSyscallParameters ps) <> semi
    pp (VarStatement _ vd) = pp vd <> semi
    pp (ConstStatement _ vd) = text "const" <+> pp vd <> semi
    pp (ReturnStatement _ e) = text "return" <+> ppMb e <> semi
    pp (ContinueStatement _) = text "continue" <> semi
    pp (BreakStatement _) = text "break" <> semi
    pp (ExpressionStatement _ e) = pp e <> semi
    
ppSyscallParameters ps = sepBy comma $ map pp ps
 
data SyscallParameter iden loc
    = SyscallPush loc (Expression iden loc)
    | SyscallReturn loc (VarName iden loc)
    | SyscallPushRef loc (VarName iden loc)
    | SyscallPushCRef loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (SyscallParameter iden loc)
    
instance Location loc => Located (SyscallParameter iden loc) where
    type LocOf (SyscallParameter iden loc) = loc
    loc (SyscallPush l _)     = l
    loc (SyscallReturn l _)   = l
    loc (SyscallPushRef l _)  = l
    loc (SyscallPushCRef l _) = l
    updLoc (SyscallPush _ x)     l = (SyscallPush l x)    
    updLoc (SyscallReturn _ x)   l = (SyscallReturn l x)  
    updLoc (SyscallPushRef _ x)  l = (SyscallPushRef l x) 
    updLoc (SyscallPushCRef _ x) l = (SyscallPushCRef l x)
  
instance PP iden => PP (SyscallParameter iden loc) where
    pp (SyscallPush _ e) = pp e
    pp (SyscallReturn _ v) = text "__return" <+> pp v
    pp (SyscallPushRef _ v) = text "__ref" <+> pp v
    pp (SyscallPushCRef _ e) = text "__cref" <+> pp e
  
-- Indices: not strictly expressions as they only appear in specific context

type Subscript iden loc = NeList (Index iden loc)

instance PP iden => PP (Subscript iden loc) where
    pp is = brackets (sepBy comma $ fmap pp is)

data Index iden loc
    = IndexSlice loc (Maybe (Expression iden loc)) (Maybe (Expression iden loc))
    | IndexInt loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Hashable iden,Hashable loc) => Hashable (Index iden loc)

instance Location loc => Located (Index iden loc) where
    type LocOf (Index iden loc) = loc
    loc (IndexSlice l _ _) = l
    loc (IndexInt l _) = l
    updLoc (IndexSlice _ x y) l = IndexSlice l x y
    updLoc (IndexInt _ x) l = IndexInt l x
  
instance PP iden => PP (Index iden loc) where
    pp (IndexSlice _ e1 e2) = ppMb e1 <+> char ':' <+> ppMb e2
    pp (IndexInt _ e) = pp e
  
-- Expressions:  

data Expression iden loc
    = BinaryAssign loc (Expression iden loc) (BinaryAssignOp loc) (Expression iden loc)
    | QualExpr loc (Expression iden loc) (SizedTypeSpecifier iden loc)
    | CondExpr loc (Expression iden loc) (Expression iden loc) (Expression iden loc)
    | BinaryExpr loc (Expression iden loc) (Op iden loc) (Expression iden loc)
    | UnaryExpr loc (Op iden loc) (Expression iden loc)
    | PreOp loc (Op iden loc) (Expression iden loc)
    | PostOp loc (Op iden loc) (Expression iden loc)
    | DomainIdExpr loc (SecTypeSpecifier iden loc)
    | BytesFromStringExpr loc (Expression iden loc)
    | StringFromBytesExpr loc (Expression iden loc)
    | VArraySizeExpr loc (Expression iden loc)
    | ProcCallExpr loc (ProcedureName iden loc) (Maybe [(TemplateTypeArgument iden loc,IsVariadic)]) [(Expression iden loc,IsVariadic)]
    | PostIndexExpr loc (Expression iden loc) (Subscript iden loc)
    | SelectionExpr loc (Expression iden loc) (AttributeName iden loc)
    | RVariablePExpr loc (VarName iden loc)
    | LitPExpr loc (Literal loc)
    | ArrayConstructorPExpr loc [Expression iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (Expression iden loc)

instance Location loc => Located (Expression iden loc) where
    type LocOf (Expression iden loc) = loc
    loc (BinaryAssign l _ _ _) = l
    loc (QualExpr l _ _) = l
    loc (CondExpr l _ _ _) = l
    loc (BinaryExpr l _ _ _) = l
    loc (PreOp l _ _) = l
    loc (PostOp l _ _) = l
    loc (UnaryExpr l _ _) = l
    loc (DomainIdExpr l _) = l
    loc (BytesFromStringExpr l _) = l
    loc (StringFromBytesExpr l _) = l
    loc (VArraySizeExpr l _) = l
    loc (ProcCallExpr l _ _ _) = l
    loc (PostIndexExpr l _ _) = l
    loc (SelectionExpr l _ _) = l
    loc (ArrayConstructorPExpr l _) = l
    loc (RVariablePExpr l _) = l
    loc (LitPExpr l _) = l
    updLoc (BinaryAssign _ x y z) l = BinaryAssign l x y z
    updLoc (QualExpr _ x y) l = QualExpr l x y
    updLoc (CondExpr _ x y z) l = CondExpr l x y z
    updLoc (BinaryExpr _ x y z) l = BinaryExpr l x y z
    updLoc (PreOp _ x y) l = PreOp l x y
    updLoc (PostOp _ x y) l = PostOp l x y
    updLoc (UnaryExpr _ x y) l = UnaryExpr l x y
    updLoc (DomainIdExpr _ x) l = DomainIdExpr l x
    updLoc (BytesFromStringExpr _ x) l = BytesFromStringExpr l x
    updLoc (StringFromBytesExpr _ x) l = StringFromBytesExpr l x
    updLoc (VArraySizeExpr _ x) l = VArraySizeExpr l x
    updLoc (ProcCallExpr _ x y z) l = ProcCallExpr l x y z
    updLoc (PostIndexExpr _ x y) l = PostIndexExpr l x y
    updLoc (SelectionExpr _ x y) l = SelectionExpr l x y
    updLoc (ArrayConstructorPExpr _ x) l = ArrayConstructorPExpr l x
    updLoc (RVariablePExpr _ x) l = RVariablePExpr l x
    updLoc (LitPExpr _ x) l = LitPExpr l x

ppVariadicArg :: (a -> Doc) -> (a,IsVariadic) -> Doc
ppVariadicArg ppA (e,v) = ppA e <> ppVariadic v
 
instance PP iden => PP (Expression iden loc) where
    pp (BinaryAssign _ post op e) = pp post <+> pp op <+> pp e
    pp (QualExpr _ e t) = pp e <+> text "::" <+> ppSizedTypeSpecifier t
    pp (CondExpr _ lor thenE elseE) = pp lor <+> char '?' <+> pp thenE <+> char ':' <+> pp elseE
    pp (BinaryExpr _ e1 o e2) = parens (pp e1 <+> pp o <+> pp e2)
    pp (PreOp _ (OpAdd _) e) = text "++" <> pp e
    pp (PreOp _ (OpSub _) e) = text "--" <> pp e
    pp (PostOp _ (OpAdd _) e) = pp e <> text "++"
    pp (PostOp _ (OpSub _) e) = pp e <> text "--"
    pp (UnaryExpr _ o e) = pp o <> pp e
    pp (DomainIdExpr _ t) = text "__domainid" <> parens (pp t)
    pp (BytesFromStringExpr _ t) = text "__bytes_from_string" <> parens (pp t)
    pp (StringFromBytesExpr _ t) = text "__string_from_bytes" <> parens (pp t)
    pp (VArraySizeExpr _ e) = text "size..." <> parens (pp e)
    pp (ProcCallExpr _ n ts es) = pp n <> ppOpt ts (\ts -> abrackets (sepBy comma $ map (ppVariadicArg pp) ts)) <> parens (sepBy comma $ map (ppVariadicArg pp) es)
    pp (PostIndexExpr _ e s) = pp e <> pp s
    pp (SelectionExpr _ e v) = pp e <> char '.' <> pp v
    pp (ArrayConstructorPExpr _ es) = braces (sepBy comma $ fmap pp es)
    pp (RVariablePExpr _ v) = pp v
    pp (LitPExpr _ l) = pp l
  
data CastType iden loc
    = CastPrim (PrimitiveDatatype loc)
    | CastTy (TypeName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable iden,Hashable loc) => Hashable (CastType iden loc)

instance Location loc => Located (CastType iden loc) where
    type LocOf (CastType iden loc) = loc
    loc (CastPrim t) = loc t
    loc (CastTy t) = loc t
    updLoc (CastPrim x) l = CastPrim $ updLoc x l
    updLoc (CastTy x) l = CastTy $ updLoc x l

instance PP iden => PP (CastType iden loc) where
    pp (CastPrim p) = pp p
    pp (CastTy v) = pp v
  
data BinaryAssignOp loc
    = BinaryAssignEqual loc
    | BinaryAssignMul   loc
    | BinaryAssignDiv   loc
    | BinaryAssignMod   loc
    | BinaryAssignAdd   loc
    | BinaryAssignSub   loc
    | BinaryAssignAnd   loc
    | BinaryAssignOr    loc
    | BinaryAssignXor   loc
  deriving (Read,Show,Data,Typeable,Eq,Ord,Functor,Generic)
  
instance (Hashable loc) => Hashable (BinaryAssignOp loc)
  
instance Location loc => Located (BinaryAssignOp loc) where
    type LocOf (BinaryAssignOp loc) = loc
    loc (BinaryAssignEqual l) = l
    loc (BinaryAssignMul   l) = l
    loc (BinaryAssignDiv   l) = l
    loc (BinaryAssignMod   l) = l
    loc (BinaryAssignAdd   l) = l
    loc (BinaryAssignSub   l) = l
    loc (BinaryAssignAnd   l) = l
    loc (BinaryAssignOr    l) = l
    loc (BinaryAssignXor   l) = l
    updLoc (BinaryAssignEqual _) l = BinaryAssignEqual l
    updLoc (BinaryAssignMul   _) l = BinaryAssignMul   l
    updLoc (BinaryAssignDiv   _) l = BinaryAssignDiv   l
    updLoc (BinaryAssignMod   _) l = BinaryAssignMod   l
    updLoc (BinaryAssignAdd   _) l = BinaryAssignAdd   l
    updLoc (BinaryAssignSub   _) l = BinaryAssignSub   l
    updLoc (BinaryAssignAnd   _) l = BinaryAssignAnd   l
    updLoc (BinaryAssignOr    _) l = BinaryAssignOr    l
    updLoc (BinaryAssignXor   _) l = BinaryAssignXor   l
  
instance PP (BinaryAssignOp loc) where
    pp (BinaryAssignEqual _) = text "="
    pp (BinaryAssignMul   _) = text "*="
    pp (BinaryAssignDiv   _) = text "/="
    pp (BinaryAssignMod   _) = text "%="
    pp (BinaryAssignAdd   _) = text "+="
    pp (BinaryAssignSub   _) = text "-="
    pp (BinaryAssignAnd   _) = text "&="
    pp (BinaryAssignOr    _) = text "|="
    pp (BinaryAssignXor   _) = text "^="
  
data Literal loc
    = IntLit loc Integer
    | StringLit loc String
    | BoolLit loc Bool
    | FloatLit loc Double
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Hashable loc) => Hashable (Literal loc)
  
instance Location loc => Located (Literal loc) where
    type LocOf (Literal loc) = loc
    loc (IntLit l _)    = l
    loc (StringLit l _) = l
    loc (BoolLit l _)   = l
    loc (FloatLit l _)  = l
    updLoc (IntLit _ x)    l = (IntLit l x)   
    updLoc (StringLit _ x) l = (StringLit l x)
    updLoc (BoolLit _ x)   l = (BoolLit l x)  
    updLoc (FloatLit _ x)  l = (FloatLit l x) 
  
instance PP (Literal loc) where
    pp (IntLit _ i) = integer i
    pp (StringLit _ s) = text (show s)
    pp (BoolLit _ b) = text (show b)
    pp (FloatLit _ f) = text (show f)

$(deriveBifunctor ''Module)
$(deriveBifunctor ''CastType)
$(deriveBifunctor ''AttributeName)
$(deriveBifunctor ''ModuleName)
$(deriveBifunctor ''TemplateArgName)
$(deriveBifunctor ''Program)
$(deriveBifunctor ''ImportDeclaration)
$(deriveBifunctor ''GlobalDeclaration)
$(deriveBifunctor ''ConstDeclaration)
$(deriveBifunctor ''ConstInitialization)
$(deriveBifunctor ''KindDeclaration)
$(deriveBifunctor ''KindName)
$(deriveBifunctor ''DomainDeclaration)
$(deriveBifunctor ''DomainName)
$(deriveBifunctor ''ProcedureName)
$(deriveBifunctor ''VarName)
$(deriveBifunctor ''TypeName)
$(deriveBifunctor ''VariableInitialization)
$(deriveBifunctor ''Sizes)
$(deriveBifunctor ''VariableDeclaration)
$(deriveBifunctor ''ProcedureParameter)
$(deriveBifunctor ''TypeSpecifier)
$(deriveBifunctor ''SecTypeSpecifier)
$(deriveBifunctor ''DatatypeSpecifier)
$(deriveBifunctor ''TemplateTypeArgument)
$(deriveBifunctor ''DimtypeSpecifier)
$(deriveBifunctor ''TemplateDeclaration)
$(deriveBifunctor ''TemplateQuantifier)
$(deriveBifunctor ''StructureDeclaration)
$(deriveBifunctor ''Attribute)
$(deriveBifunctor ''ReturnTypeSpecifier)
$(deriveBifunctor ''ProcedureDeclaration)
$(deriveBifunctor ''ForInitializer)
$(deriveBifunctor ''Statement)
$(deriveBifunctor ''SyscallParameter)
$(deriveBifunctor ''Index)
$(deriveBifunctor ''Expression) 
$(deriveBifunctor ''Op) 

unaryLitExpr :: Expression iden loc -> Expression iden loc
unaryLitExpr (UnaryExpr l (OpSub _) (LitPExpr _ (IntLit l1 i))) = LitPExpr l $ IntLit l1 (-i)
unaryLitExpr (UnaryExpr l (OpSub _) (LitPExpr _ (FloatLit l1 f))) = LitPExpr l $ FloatLit l1 (-f)
unaryLitExpr e = e
    
instance PP iden => PP [Expression iden loc] where
    pp xs = parens $ sepBy comma $ map pp xs
    
instance PP iden => PP [(Expression iden loc, IsVariadic)] where
    pp xs = parens $ sepBy comma $ map (ppVariadicArg pp) xs
    
    