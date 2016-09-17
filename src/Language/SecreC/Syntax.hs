{-# LANGUAGE ScopedTypeVariables, DeriveGeneric, TemplateHaskell, TypeFamilies, DeriveFoldable, DeriveTraversable, DeriveFunctor, MultiParamTypeClasses, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances #-}

module Language.SecreC.Syntax where

import Data.Traversable
import Data.Foldable as Foldable
import Data.Generics hiding (empty,Generic)
import Data.Bifunctor.TH
import Data.Hashable
import Data.Binary

import Text.PrettyPrint as PP

import GHC.Generics (Generic)

import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Utils

import Control.Monad

-- Program and variable declarations:                                          

data Module iden loc = Module loc (Maybe (ModuleName iden loc)) (Program iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (Module iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (Module iden loc)

moduleFile :: Location loc => Module iden loc -> String
moduleFile (Module l _ _) = posFileName $ locpos l

moduleIdMb :: Module iden loc -> Maybe iden
moduleIdMb (Module _ Nothing _) = Nothing
moduleIdMb (Module _ (Just (ModuleName _ n)) _) = Just n

moduleId :: Module Identifier loc -> Identifier
moduleId = maybe "main" id . moduleIdMb

addModuleImport :: ImportDeclaration iden loc -> Module iden loc -> Module iden loc
addModuleImport i (Module l n p) = Module l n (addProgramImport i p)

moduleImports :: Module iden loc -> [ImportDeclaration iden loc]
moduleImports (Module _ _ p) = programImports p

instance Location loc => Located (Module iden loc) where
    type LocOf (Module iden loc) = loc
    loc (Module l _ _) = l
    updLoc (Module _ x y) l = Module l x y

instance PP m iden => PP m (Module iden loc) where
    pp (Module _ (Just modulename) prog) = do
        pp1 <- pp modulename
        pp2 <- pp prog
        return $ text "module" <+> pp1 <+> text "where" $$ pp2
    pp (Module _ Nothing prog) = pp prog

data AttributeName iden loc = AttributeName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (AttributeName iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (AttributeName iden loc)

moduleNameId :: ModuleName iden loc -> iden
moduleNameId (ModuleName _ i) = i
  
attributeNameId :: AttributeName iden loc -> iden
attributeNameId (AttributeName _ i) = i
  
instance Location loc => Located (AttributeName iden loc) where
    type LocOf (AttributeName iden loc) = loc
    loc (AttributeName l _) = l
    updLoc (AttributeName _ x) l = AttributeName l x
  
instance PP m iden => PP m (AttributeName iden loc) where
    pp (AttributeName _ iden) = pp iden

data ModuleName iden loc = ModuleName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (ModuleName iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ModuleName iden loc)
  
instance Location loc => Located (ModuleName iden loc) where
    type LocOf (ModuleName iden loc) = loc
    loc (ModuleName l _) = l
    updLoc (ModuleName _ x) l = ModuleName l x
  
instance PP m iden => PP m (ModuleName iden loc) where
    pp (ModuleName _ iden) = pp iden

data TemplateArgName iden loc = TemplateArgName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (TemplateArgName iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (TemplateArgName iden loc)
  
instance Location loc => Located (TemplateArgName iden loc) where
    type LocOf (TemplateArgName iden loc) = loc
    loc (TemplateArgName l _) = l
    updLoc (TemplateArgName _ x) l = TemplateArgName l x
  
instance PP m iden => PP m (TemplateArgName iden loc) where
    pp (TemplateArgName _ iden) = pp iden

data Program iden loc = Program loc [ImportDeclaration iden loc] [GlobalDeclaration iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (Program iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (Program iden loc)

addProgramImport :: ImportDeclaration iden loc -> Program iden loc -> Program iden loc
addProgramImport i (Program l is gs) = Program l (i:is) gs

programImports :: Program iden loc -> [ImportDeclaration iden loc]
programImports (Program _ is _) = is
  
instance Location loc => Located (Program iden loc) where
    type LocOf (Program iden loc) = loc
    loc (Program l _ _) = l
    updLoc (Program _ x y) l = Program l x y
  
instance PP m iden => PP m (Program iden loc) where
    pp (Program _ is gs) = do
        pp1 <- pp is
        pp2 <- pp gs
        return $ pp1 $$ pp2

instance PP m iden => PP m [ImportDeclaration iden loc] where
    pp is = liftM vcat $ mapM pp is

instance PP m iden => PP m [GlobalDeclaration iden loc] where
    pp gs = liftM vcat $ mapM pp gs

data ImportDeclaration iden loc = Import loc (ModuleName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (ImportDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ImportDeclaration iden loc)
  
instance Location loc => Located (ImportDeclaration iden loc) where
    type LocOf (ImportDeclaration iden loc) = loc
    loc (Import l _) = l
    updLoc (Import _ x) l = Import l x
 
instance PP m iden => PP m (ImportDeclaration iden loc) where
    pp (Import _ modulename) = liftM (text "import" <+>) (pp modulename)

data GlobalDeclaration iden loc
    = GlobalVariable loc (VariableDeclaration iden loc)
    | GlobalDomain loc (DomainDeclaration iden loc)
    | GlobalKind loc (KindDeclaration iden loc)
    | GlobalProcedure loc (ProcedureDeclaration iden loc)
    | GlobalStructure loc (StructureDeclaration iden loc)
    | GlobalFunction loc (FunctionDeclaration iden loc)
    | GlobalTemplate loc (TemplateDeclaration iden loc)
    | GlobalAnnotations loc [GlobalAnnotation iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (GlobalDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (GlobalDeclaration iden loc)

instance Location loc => Located (GlobalDeclaration iden loc) where
    type LocOf (GlobalDeclaration iden loc) = loc
    loc (GlobalVariable l vd) = l
    loc (GlobalDomain l dd) = l
    loc (GlobalKind l kd) = l
    loc (GlobalProcedure l pd) = l
    loc (GlobalFunction l pd) = l
    loc (GlobalStructure l sd) = l
    loc (GlobalTemplate l td) = l
    loc (GlobalAnnotations l ann) = l
    updLoc (GlobalVariable _ vd) l = GlobalVariable l vd
    updLoc (GlobalDomain _ dd) l = GlobalDomain l dd
    updLoc (GlobalKind _ kd) l = GlobalKind l kd
    updLoc (GlobalProcedure _ pd) l = GlobalProcedure l pd
    updLoc (GlobalFunction _ pd) l = GlobalFunction l pd
    updLoc (GlobalStructure _ sd) l = GlobalStructure l sd
    updLoc (GlobalTemplate _ td) l = GlobalTemplate l td
    updLoc (GlobalAnnotations _ ann) l = GlobalAnnotations l ann

instance PP m iden => PP m (GlobalDeclaration iden loc) where
    pp (GlobalVariable _ vd) = pp vd
    pp (GlobalDomain _ dd) = pp dd
    pp (GlobalKind _ kd) = pp kd
    pp (GlobalProcedure _ pd) = pp pd
    pp (GlobalFunction _ f) = pp f
    pp (GlobalStructure _ sd) = pp sd
    pp (GlobalTemplate _ td) = pp td
    pp (GlobalAnnotations _ ann) = pp ann

data KindDeclaration iden loc = Kind loc (KindName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (KindDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (KindDeclaration iden loc)
 
instance Location loc => Located (KindDeclaration iden loc) where
    type LocOf (KindDeclaration iden loc) = loc
    loc (Kind l _) = l
    updLoc (Kind _ x) l = Kind l x
 
instance PP m iden => PP m (KindDeclaration iden loc) where
    pp (Kind _ kname) = do
        ppk <- pp kname
        return $ text "kind" <+> ppk
  
data KindName iden loc = KindName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (KindName iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (KindName iden loc)

kindId :: KindName iden loc -> iden
kindId (KindName _ n) = n

instance Location loc => Located (KindName iden loc) where
    type LocOf (KindName iden loc) = loc
    loc (KindName l _) = l
    updLoc (KindName _ x) l = KindName l x

instance PP m iden => PP m (KindName iden loc) where
    pp (KindName _ iden) = pp iden

data DomainDeclaration iden loc = Domain loc (DomainName iden loc) (KindName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (DomainDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (DomainDeclaration iden loc)

instance Location loc => Located (DomainDeclaration iden loc) where
    type LocOf (DomainDeclaration iden loc) = loc
    loc (Domain l _ _) = l
    updLoc (Domain _ x y) l = Domain l x y

instance PP m iden => PP m (DomainDeclaration iden loc) where
    pp (Domain _ dom kind) = do
        ppd <- pp dom
        ppk <- pp kind
        return $ text "domain" <+> ppd <+> ppk
 
data DomainName iden loc = DomainName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (DomainName iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (DomainName iden loc)

instance Location loc => Located (DomainName iden loc) where
    type LocOf (DomainName iden loc) = loc
    loc (DomainName l _) = l
    updLoc (DomainName _ x) l = DomainName l x

instance PP m iden => PP m (DomainName iden loc) where
    pp (DomainName _ iden) = pp iden

data ProcedureName iden loc = ProcedureName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary iden,Binary loc) => Binary (ProcedureName iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ProcedureName iden loc)
  
instance Location loc => Located (ProcedureName iden loc) where
    type LocOf (ProcedureName iden loc) = loc
    loc (ProcedureName l _) = l
    updLoc (ProcedureName _ x) l = ProcedureName l x
 
instance PP m iden => PP m (ProcedureName iden loc) where
    pp (ProcedureName _ iden) = pp iden

data VarName iden loc = VarName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic,Traversable,Foldable)

instance (Binary iden,Binary loc) => Binary (VarName iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (VarName iden loc)

varNameId :: VarName iden loc -> iden
varNameId (VarName _ i) = i

procedureNameId :: ProcedureName iden loc -> iden
procedureNameId (ProcedureName _ i) = i
  
instance Location loc => Located (VarName iden loc) where
    type LocOf (VarName iden loc) = loc
    loc (VarName l _) = l
    updLoc (VarName _ x) l = VarName l x
 
instance PP m iden => PP m (VarName iden loc) where
    pp (VarName _ iden) = pp iden

data TypeName iden loc = TypeName loc iden
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (TypeName iden loc)
instance (Hashable iden,Hashable loc) => Hashable (TypeName iden loc)

typeId :: TypeName iden loc -> iden
typeId (TypeName _ i) = i

instance Location loc => Located (TypeName iden loc) where
    type LocOf (TypeName iden loc) = loc
    loc (TypeName l _) = l
    updLoc (TypeName _ x) l = TypeName l x

instance PP m iden => PP m (TypeName iden loc) where
    pp (TypeName _ iden) = pp iden

type Identifier = String

instance Monad m => PP m String where
    pp s = return $ text s

data VariableInitialization iden loc = VariableInitialization loc (VarName iden loc) (Maybe (Sizes iden loc)) (Maybe (Expression iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (VariableInitialization iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (VariableInitialization iden loc)
  
instance Location loc => Located (VariableInitialization iden loc) where
    type LocOf (VariableInitialization iden loc) = loc
    loc (VariableInitialization l _ _ _) = l
    updLoc (VariableInitialization _ x y z) l = VariableInitialization l x y z
 
instance PP m iden => PP m (VariableInitialization iden loc) where
    pp (VariableInitialization _ v dim ex) = do
        ppv <- pp v
        ppe <- ppExp ex
        ppd <- ppSizes dim
        return $ ppv <+> ppd <+> ppe
      where
        ppSizes Nothing = return $ empty
        ppSizes (Just szs) = pp szs
        ppExp Nothing = return $ empty
        ppExp (Just e) = liftM (text "=" <+>) (pp e)

newtype Sizes iden loc = Sizes (NeList (Expression iden loc,IsVariadic))
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (Sizes iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (Sizes iden loc)
  
unSizes (Sizes xs) = xs
sizesList = Foldable.toList . unSizes

instance Functor (Sizes iden) where
    fmap f (Sizes xs) = Sizes $ fmap (\(x,y) -> (fmap f x,y)) xs

instance Location loc => Located (Sizes iden loc) where
    type LocOf (Sizes iden loc) = loc
    loc (Sizes xs) = loc (fst $ headNe xs)
    updLoc (Sizes xs) l = Sizes (updHeadNe (\(x,y) -> (updLoc x l,y)) xs)

instance PP m iden => PP m (Sizes iden loc) where
    pp (Sizes es) = do
        pps <- mapM (ppVariadicArg pp) es
        return $ parens (sepBy comma pps)

type IsConst = Bool
type IsHavoc = Bool

data VariableDeclaration iden loc = VariableDeclaration loc IsConst IsHavoc (TypeSpecifier iden loc) (NeList (VariableInitialization iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary iden,Binary loc) => Binary (VariableDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (VariableDeclaration iden loc)

instance Location loc => Located (VariableDeclaration iden loc) where
    type LocOf (VariableDeclaration iden loc) = loc
    loc (VariableDeclaration l _ _ _ _) = l
    updLoc (VariableDeclaration _ isConst isHavoc x y) l = VariableDeclaration l isConst isHavoc x y

instance PP m iden => PP m (VariableDeclaration iden loc) where
    pp (VariableDeclaration _ isConst isHavoc t is) = do
        ppt <- pp t
        ppis <- mapM pp is
        return $ ppConst isConst (ppHavoc isHavoc (ppt <+> sepBy comma ppis))

type IsVariadic = Bool

data ProcedureParameter iden loc
    = ProcedureParameter loc IsConst (TypeSpecifier iden loc) IsVariadic (VarName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary iden,Binary loc) => Binary (ProcedureParameter iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ProcedureParameter iden loc)

instance Location loc => Located (ProcedureParameter iden loc) where
    type LocOf (ProcedureParameter iden loc) = loc
    loc (ProcedureParameter l _ _ _ _) = l
    updLoc (ProcedureParameter _ isConst isHavoc x y) l = ProcedureParameter l isConst isHavoc x y

instance PP m iden => PP m (ProcedureParameter iden loc) where
    pp (ProcedureParameter _ isConst t b v) = do
        ppt <- pp t
        ppv <- pp v
        return $ ppConst isConst (ppVariadic ppt b <+> ppv)

ppConst True doc = text "const" <+> doc
ppConst False doc = doc
ppHavoc True doc = text "havoc" <+> doc
ppHavoc False doc = doc

-- Types:                                                                      

data TypeSpecifier iden loc = TypeSpecifier loc (Maybe (SecTypeSpecifier iden loc)) (DatatypeSpecifier iden loc) (Maybe (DimtypeSpecifier iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary iden,Binary loc) => Binary (TypeSpecifier iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (TypeSpecifier iden loc)
  
typeSpecifierLoc :: TypeSpecifier iden loc -> loc
typeSpecifierLoc (TypeSpecifier l _ _ _) = l

instance Location loc => Located (TypeSpecifier iden loc) where
    type LocOf (TypeSpecifier iden loc) = loc
    loc (TypeSpecifier l _ _ _) = l
    updLoc (TypeSpecifier _ x y z) l = TypeSpecifier l x y z
  
instance PP m iden => PP m (TypeSpecifier iden loc) where
    pp (TypeSpecifier _ sec t dim) = do
        pps <- ppMb sec
        ppt <- pp t
        ppd <- ppMb dim
        return $ pps <+> ppt <+> ppd

data SecTypeSpecifier iden loc
    = PublicSpecifier loc
    | PrivateSpecifier loc (DomainName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (SecTypeSpecifier iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (SecTypeSpecifier iden loc)

instance Location loc => Located (SecTypeSpecifier iden loc) where
    type LocOf (SecTypeSpecifier iden loc) = loc
    loc (PublicSpecifier l) = l
    loc (PrivateSpecifier l _) = l
    updLoc (PublicSpecifier _) l = PublicSpecifier l
    updLoc (PrivateSpecifier _ x) l = PrivateSpecifier l x

instance PP m iden => PP m (SecTypeSpecifier iden loc) where
    pp (PublicSpecifier _) = return $ text "public"
    pp (PrivateSpecifier _ n) = pp n

data DatatypeSpecifier iden loc
    = PrimitiveSpecifier loc (PrimitiveDatatype loc)
    | TemplateSpecifier loc (TypeName iden loc) [(TemplateTypeArgument iden loc,IsVariadic)]
    | MultisetSpecifier loc (DatatypeSpecifier iden loc)
    | VariableSpecifier loc (TypeName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (DatatypeSpecifier iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (DatatypeSpecifier iden loc)

instance Location loc => Located (DatatypeSpecifier iden loc) where
    type LocOf (DatatypeSpecifier iden loc) = loc
    loc (PrimitiveSpecifier l _) = l
    loc (TemplateSpecifier l _ _) = l
    loc (MultisetSpecifier l _) = l
    loc (VariableSpecifier l _) = l
    updLoc (PrimitiveSpecifier _ x) l = PrimitiveSpecifier l x
    updLoc (TemplateSpecifier _ x y) l = TemplateSpecifier l x y
    updLoc (VariableSpecifier _ x) l = VariableSpecifier l x
    updLoc (MultisetSpecifier _ x) l = MultisetSpecifier l x

instance PP m iden => PP m (DatatypeSpecifier iden loc) where
    pp (PrimitiveSpecifier _ prim) = pp prim
    pp (TemplateSpecifier _ t args) = do
        ppt <- pp t
        ppas <- mapM (ppVariadicArg pp) args
        return $ ppt <> abrackets (sepBy comma ppas)
    pp (VariableSpecifier _ tn) = pp tn
    pp (MultisetSpecifier _ b) = do
        pp1 <- pp b
        return $ text "multiset" <> abrackets pp1

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

instance Binary loc => Binary (PrimitiveDatatype loc)
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

instance Monad m => PP m (PrimitiveDatatype loc) where
    pp (DatatypeBool       _) = return $ text "bool"
    pp (DatatypeInt8       _) = return $ text "int8"
    pp (DatatypeUint8      _) = return $ text "uint8"
    pp (DatatypeInt16      _) = return $ text "int16"
    pp (DatatypeUint16     _) = return $ text "uint16"
    pp (DatatypeInt32      _) = return $ text "int32"
    pp (DatatypeUint32     _) = return $ text "uint32"
    pp (DatatypeInt64      _) = return $ text "int64"
    pp (DatatypeUint64     _) = return $ text "uint64"
    pp (DatatypeString     _) = return $ text "string"
    pp (DatatypeXorUint8   _) = return $ text "xor_uint8"
    pp (DatatypeXorUint16  _) = return $ text "xor_uint16"
    pp (DatatypeXorUint32  _) = return $ text "xor_uint32"
    pp (DatatypeXorUint64  _) = return $ text "xor_uint64"
    pp (DatatypeFloat32    _) = return $ text "float32"
    pp (DatatypeFloat64    _) = return $ text "float64"
  
data TemplateTypeArgument iden loc
    = GenericTemplateTypeArgument loc (TemplateArgName iden loc)
    | TemplateTemplateTypeArgument loc (TypeName iden loc) [(TemplateTypeArgument iden loc,IsVariadic)]
    | PrimitiveTemplateTypeArgument loc (PrimitiveDatatype loc)
    | ExprTemplateTypeArgument loc (Expression iden loc)
    | PublicTemplateTypeArgument loc
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (TemplateTypeArgument iden loc)  
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

instance PP m iden => PP m (TemplateTypeArgument iden loc) where
    pp (GenericTemplateTypeArgument _ targ) = pp targ
    pp (TemplateTemplateTypeArgument _ t args) = do
        ppt <- pp t
        ppas <- mapM (ppVariadicArg pp) args
        return $ ppt <> abrackets (sepBy comma ppas)
    pp (PrimitiveTemplateTypeArgument _ prim) = pp prim
    pp (ExprTemplateTypeArgument _ e) = pp e
    pp (PublicTemplateTypeArgument _) = return $ text "public"
  
data DimtypeSpecifier iden loc
    = DimSpecifier loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (DimtypeSpecifier iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (DimtypeSpecifier iden loc)
  
instance Location loc => Located (DimtypeSpecifier iden loc) where
    type LocOf (DimtypeSpecifier iden loc) = loc
    loc (DimSpecifier l _) = l
    updLoc (DimSpecifier _ x) l = DimSpecifier l x
  
instance PP m iden => PP m (DimtypeSpecifier iden loc) where
    pp (DimSpecifier _ n) = do
        ppn <- pp n
        return $ brackets $ brackets ppn
  
-- Templates:                                                                  

data TemplateDeclaration iden loc
    = TemplateStructureDeclaration loc [TemplateQuantifier iden loc] (StructureDeclaration iden loc)
    | TemplateStructureSpecialization loc [TemplateQuantifier iden loc] [(TemplateTypeArgument iden loc,IsVariadic)] (StructureDeclaration iden loc)
    | TemplateProcedureDeclaration loc [TemplateQuantifier iden loc] (ProcedureDeclaration iden loc)
    | TemplateFunctionDeclaration loc [TemplateQuantifier iden loc] (FunctionDeclaration iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (TemplateDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (TemplateDeclaration iden loc)
  
instance Location loc => Located (TemplateDeclaration iden loc) where
    type LocOf (TemplateDeclaration iden loc) = loc
    loc (TemplateStructureDeclaration l _ _) = l
    loc (TemplateStructureSpecialization l _ _ _) = l
    loc (TemplateProcedureDeclaration l _ _) = l
    loc (TemplateFunctionDeclaration l _ _) = l
    updLoc (TemplateStructureDeclaration _ x y) l = TemplateStructureDeclaration l x y
    updLoc (TemplateStructureSpecialization _ x y z) l = TemplateStructureSpecialization l x y z
    updLoc (TemplateProcedureDeclaration _ x y) l = TemplateProcedureDeclaration l x y
    updLoc (TemplateFunctionDeclaration _ x y) l = TemplateFunctionDeclaration l x y
  
instance PP m iden => PP m (TemplateDeclaration iden loc) where
    pp (TemplateStructureDeclaration _ qs struct) = do
        pp1 <- mapM pp qs
        pp2 <- ppStruct Nothing struct
        return $ text "template" <+> abrackets (sepBy comma pp1) <+> pp2
    pp (TemplateStructureSpecialization _ qs specials struct) = do
        pp1 <- mapM pp qs
        pp2 <- ppStruct (Just specials) struct
        return $ text "template" <+> abrackets (sepBy comma pp1) <+> pp2
    pp (TemplateProcedureDeclaration _ qs proc) = do
        pp1 <- mapM pp qs
        pp2 <- pp proc
        return $ text "template" <+> abrackets (sepBy comma pp1) <+> pp2
    pp (TemplateFunctionDeclaration _ qs proc) = do
        pp1 <- mapM pp qs
        pp2 <- pp proc
        return $ text "template" <+> abrackets (sepBy comma pp1) <+> pp2
  
data TemplateQuantifier iden loc
    = DomainQuantifier loc IsVariadic (DomainName iden loc) (Maybe (KindName iden loc))
    | KindQuantifier loc Bool IsVariadic (KindName iden loc)
    | DimensionQuantifier loc IsVariadic (VarName iden loc) (Maybe (Expression iden loc))
    | DataQuantifier loc IsVariadic (TypeName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (TemplateQuantifier iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (TemplateQuantifier iden loc)

instance Location loc => Located (TemplateQuantifier iden loc) where
    type LocOf (TemplateQuantifier iden loc) = loc
    loc (DomainQuantifier l _ _ _) = l
    loc (KindQuantifier l _ _ _) = l
    loc (DimensionQuantifier l _ _ _) = l
    loc (DataQuantifier l _ _) = l
    updLoc (DomainQuantifier _ b x y) l = DomainQuantifier l b x y
    updLoc (KindQuantifier _ b0 b x) l = KindQuantifier l b0 b x
    updLoc (DimensionQuantifier _ b x y) l = DimensionQuantifier l b x y
    updLoc (DataQuantifier _ b x) l = DataQuantifier l b x

instance PP m iden => PP m (TemplateQuantifier iden loc) where
    pp (DomainQuantifier _ b d (Just k)) = do
        pp1 <- pp d
        pp2 <- pp k
        return $ ppVariadic (text "domain") b <+> pp1 <+> char ':' <+> pp2
    pp (DomainQuantifier _ b d Nothing) = do
        pp1 <- pp d
        return $ ppVariadic (text "domain") b <+> pp1
    pp (DimensionQuantifier _ b dim e) = do
        ppd <- pp dim
        pp2 <- ppOpt e (liftM braces . pp)
        return $ ppVariadic (text "dim") b <+> ppd <+> pp2
    pp (DataQuantifier _ b t) = do
        ppt <- pp t
        return $ ppVariadic (text "type") b <+> ppt
    pp (KindQuantifier _ isPrivate isVariadic k) = do
        ppk <- pp k
        ppIsPrivate isPrivate (return $ ppVariadic (text "kind") isVariadic <+> ppk)
  
ppIsPrivate False doc = doc
ppIsPrivate True doc = liftM (text "nonpublic" <+>) doc
  
 -- Structures:                                                                

data StructureDeclaration iden loc = StructureDeclaration loc (TypeName iden loc) [Attribute iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (StructureDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (StructureDeclaration iden loc)

structureDeclarationId :: StructureDeclaration iden loc -> iden
structureDeclarationId (StructureDeclaration _ tn _) = typeId tn
 
instance Location loc => Located (StructureDeclaration iden loc) where
    type LocOf (StructureDeclaration iden loc) = loc
    loc (StructureDeclaration l _ _) = l
    updLoc (StructureDeclaration _ x y) l = StructureDeclaration l x y
  
instance PP m iden => PP m (StructureDeclaration iden loc) where
    pp s = ppStruct Nothing s
  
ppStruct :: PP m iden => Maybe [(TemplateTypeArgument iden loc,IsVariadic)] -> StructureDeclaration iden loc -> m Doc
ppStruct Nothing (StructureDeclaration _ t as) = do
    ppt <- pp t
    ppas <- mapM pp as
    return $ text "struct" <+> ppt <+> braces (vcat ppas)
ppStruct (Just specials) (StructureDeclaration _ t as) = do
    ppt <- pp t
    pp2 <- mapM (ppVariadicArg pp) specials
    ppas <- mapM pp as
    return $ text "struct" <+> ppt <+> abrackets (sepBy comma pp2) <+> braces (vcat ppas)
  
data Attribute iden loc = Attribute loc (TypeSpecifier iden loc) (AttributeName iden loc) (Maybe (Sizes iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

attributeName :: Attribute iden loc -> AttributeName iden loc
attributeName (Attribute _ t a szs) = a

instance (Binary iden,Binary loc) => Binary (Attribute iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (Attribute iden loc)
 
instance Location loc => Located (Attribute iden loc) where
    type LocOf (Attribute iden loc) = loc
    loc (Attribute l _ _ _) = l
    updLoc (Attribute _ x y z) l = Attribute l x y z
  
instance PP m iden => PP m (Attribute iden loc) where
    pp (Attribute _ t v szs) = do
        ppt <- pp t
        ppv <- pp v
        ppszs <- ppSizes szs
        return $ ppt <+> ppv <> ppszs <> char ';'
      where
        ppSizes Nothing = return PP.empty
        ppSizes (Just szs) = pp szs

-- Procedures:

data ReturnTypeSpecifier iden loc = ReturnType loc (Maybe (TypeSpecifier iden loc))
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (ReturnTypeSpecifier iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ReturnTypeSpecifier iden loc)

instance Location loc => Located (ReturnTypeSpecifier iden loc) where
    type LocOf (ReturnTypeSpecifier iden loc) = loc
    loc (ReturnType l _) = l
    updLoc (ReturnType _ x) l = ReturnType l x
 
instance PP m iden => PP m (ReturnTypeSpecifier iden loc) where
    pp (ReturnType loc Nothing) = return $ text "void"
    pp (ReturnType loc (Just t)) = pp t
  
data ProcedureDeclaration iden loc
    = OperatorDeclaration loc
        (ReturnTypeSpecifier iden loc)
        (Op iden loc)
        [ProcedureParameter iden loc]
        [ProcedureAnnotation iden loc]
        [Statement iden loc]
    | ProcedureDeclaration loc
        (ReturnTypeSpecifier iden loc)
        (ProcedureName iden loc)
        [ProcedureParameter iden loc]
        [ProcedureAnnotation iden loc]
        [Statement iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (ProcedureDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ProcedureDeclaration iden loc)

instance Location loc => Located (ProcedureDeclaration iden loc) where
    type LocOf (ProcedureDeclaration iden loc) = loc
    loc (OperatorDeclaration l _ _ _ _ _) = l
    loc (ProcedureDeclaration l _ _ _ _ _) = l
    updLoc (OperatorDeclaration _ x y z w s) l = OperatorDeclaration l x y z w s
    updLoc (ProcedureDeclaration _ x y z w s) l = ProcedureDeclaration l x y z w s
  
instance PP m iden => PP m (ProcedureDeclaration iden loc) where
    pp (OperatorDeclaration _ ret op params anns stmts) = do
        pp0 <- pp ret
        pp1 <- pp op
        pp2 <- mapM pp params
        pp3 <- pp anns
        pp4 <- pp stmts
        return $ pp0 <+> text "operator" <+> pp1 <+> parens (sepBy comma pp2) $+$ pp3 $+$ lbrace $+$ nest 4 pp4 $+$ rbrace
    pp (ProcedureDeclaration _ ret proc params anns stmts) = do
        pp1 <- pp ret
        pp2 <- pp proc
        pp3 <- mapM pp params
        pp4 <- pp anns
        pp5 <- pp stmts
        return $ pp1 <+> pp2 <+> parens (sepBy comma pp3) $+$ pp4 $+$ lbrace $+$ nest 4 pp5 $+$ rbrace
    
data AxiomDeclaration iden loc
    = AxiomDeclaration loc
        Bool -- is leakage
        [TemplateQuantifier iden loc] -- template arguments
        [ProcedureParameter iden loc]
        [ProcedureAnnotation iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (AxiomDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (AxiomDeclaration iden loc)

instance Location loc => Located (AxiomDeclaration iden loc) where
    type LocOf (AxiomDeclaration iden loc) = loc
    loc (AxiomDeclaration l _ _ _ _) = l
    updLoc (AxiomDeclaration _ isLeak x y z) l = AxiomDeclaration l isLeak x y z
  
instance PP m iden => PP m (AxiomDeclaration iden loc) where
    pp (AxiomDeclaration _ isLeak qs params anns) = do
        pp1 <- mapM pp qs
        pp2 <- mapM pp params
        pp3 <- pp anns
        return $ ppLeak isLeak (text "axiom" <+> abrackets (sepBy comma pp1) <+> parens (sepBy comma pp2) $+$ pp3 )

data LemmaDeclaration iden loc
    = LemmaDeclaration loc
        Bool -- is leakage
        (ProcedureName iden loc)
        [TemplateQuantifier iden loc] -- template arguments
        [ProcedureParameter iden loc]
        [ProcedureAnnotation iden loc]
        (Maybe [Statement iden loc])
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary iden,Binary loc) => Binary (LemmaDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (LemmaDeclaration iden loc)

instance Location loc => Located (LemmaDeclaration iden loc) where
    type LocOf (LemmaDeclaration iden loc) = loc
    loc (LemmaDeclaration l _ _ _ _ _ _) = l
    updLoc (LemmaDeclaration _ isLeak n x y z ss) l = LemmaDeclaration l isLeak n x y z ss
  
instance PP m iden => PP m (LemmaDeclaration iden loc) where
    pp (LemmaDeclaration _ isLeak n qs params anns body) = do
        pp1 <- pp n
        pp2 <- mapM pp qs
        pp3 <- mapM pp params
        pp4 <- pp anns
        pp5 <- ppOpt body (\stmts -> do { x <- pp stmts; return $ lbrace $+$ nest 4 x $+$ rbrace })
        return $ ppLeak isLeak (text "lemma" <+> pp1 <+> abrackets (sepBy comma pp2) <+> parens (sepBy comma pp3) $+$ pp4 $+$ pp5)

data FunctionDeclaration iden loc
    = OperatorFunDeclaration loc
        Bool -- is leakage
        (TypeSpecifier iden loc)
        (Op iden loc)
        [ProcedureParameter iden loc]
        [ProcedureAnnotation iden loc]
        (Expression iden loc)
    | FunDeclaration loc
        Bool -- is leakage
        (TypeSpecifier iden loc)
        (ProcedureName iden loc)
        [ProcedureParameter iden loc]
        [ProcedureAnnotation iden loc]
        (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (FunctionDeclaration iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (FunctionDeclaration iden loc)

instance Location loc => Located (FunctionDeclaration iden loc) where
    type LocOf (FunctionDeclaration iden loc) = loc
    loc (OperatorFunDeclaration l _ _ _ _ _ _) = l
    loc (FunDeclaration l _ _ _ _ _ _) = l
    updLoc (OperatorFunDeclaration _ isLeak x y z w s) l = OperatorFunDeclaration l isLeak x y z w s
    updLoc (FunDeclaration _ isLeak x y z w s) l = FunDeclaration l isLeak x y z w s
  
instance PP m iden => PP m (FunctionDeclaration iden loc) where
    pp (OperatorFunDeclaration _ isLeak ret op params anns stmts) = do
        pp1 <- pp ret
        pp2 <- pp op
        pp3 <- mapM pp params
        pp4 <- pp anns
        pp5 <- pp stmts
        return $ ppLeak isLeak (text "function" <+> pp1 <+> text "operator" <+> pp2 <+> parens (sepBy comma pp3) $+$ pp4 $+$ lbrace $+$ nest 4 pp5 $+$ rbrace)
    pp (FunDeclaration _ isLeak ret proc params anns stmts) = do
        ppr <- pp ret
        ppp <- pp proc
        pas <- mapM pp params
        p1 <- pp anns
        p2 <- pp stmts
        return $ ppLeak isLeak (text "function" <+> ppr <+> ppp <+> parens (sepBy comma pas) $+$ p1 $+$ lbrace $+$ nest 4 p2 $+$ rbrace)
  
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
    | OpImplies  loc
    | OpEquiv    loc
  deriving (Read,Show,Data,Typeable,Eq,Ord,Functor,Generic)

instance (Binary iden,Binary loc) => Binary (Op iden loc)

instance (Hashable iden,Hashable loc) => Hashable (Op iden loc)

isBoolOp :: Op iden loc -> Bool
isBoolOp (OpLor _) = True
isBoolOp (OpNot _) = True
isBoolOp (OpXor _) = True
isBoolOp (OpLand _) = True
isBoolOp (OpImplies _) = True
isBoolOp (OpEquiv _) = True
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

instance PP m iden => PP m (Op iden loc) where
    pp (OpAdd  l) =     return $ text "+"
    pp (OpBand l) =     return $ text "&" 
    pp (OpBor  l) =     return $ text "|" 
    pp (OpDiv  l) =     return $ text "/" 
    pp (OpGt   l) =     return $ text ">" 
    pp (OpLt   l) =     return $ text "<" 
    pp (OpMod  l) =     return $ text "%" 
    pp (OpMul  l) =     return $ text "*" 
    pp (OpSub  l) =     return $ text "-" 
    pp (OpXor  l) =     return $ text "^" 
    pp (OpEq   l) =     return $ text "==" 
    pp (OpGe   l) =     return $ text ">=" 
    pp (OpLand l) =     return $ text "&&" 
    pp (OpLe   l) =     return $ text "<=" 
    pp (OpLor  l) =     return $ text "||" 
    pp (OpNe   l) =     return $ text "!=" 
    pp (OpShl  l) =     return $ text "<<" 
    pp (OpShr  l) =     return $ text ">>" 
    pp (OpNot l) =      return $ text "!"
    pp (OpCast l t) =   liftM parens (pp t)
    pp (OpInv l) =      return $ text "~"
    pp (OpImplies l) =  return $ text "==>"
    pp (OpEquiv l) =    return $ text "<==>"
  
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
    loc (OpImplies l)  = l
    loc (OpEquiv l)  = l
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
    updLoc (OpImplies  _) l = OpImplies  l
    updLoc (OpEquiv  _) l = OpEquiv  l
  
-- Statements: 

data ForInitializer iden loc
    = InitializerExpression (Maybe (Expression iden loc))
    | InitializerVariable (VariableDeclaration iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (ForInitializer iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ForInitializer iden loc)
 
instance PP m iden => PP m (ForInitializer iden loc) where
    pp (InitializerExpression e) = ppMb e
    pp (InitializerVariable v) = pp v

data Statement iden loc
    = CompoundStatement loc [Statement iden loc]
    | IfStatement loc (Expression iden loc) (Statement iden loc) (Maybe (Statement iden loc))
    | ForStatement loc (ForInitializer iden loc) (Maybe (Expression iden loc)) (Maybe (Expression iden loc)) [LoopAnnotation iden loc] (Statement iden loc)
    | WhileStatement loc (Expression iden loc) [LoopAnnotation iden loc] (Statement iden loc)
    | PrintStatement loc [(Expression iden loc,IsVariadic)]
    | DowhileStatement loc [LoopAnnotation iden loc] (Statement iden loc) (Expression iden loc)
    | AssertStatement loc (Expression iden loc)
    | SyscallStatement loc String [SyscallParameter iden loc]
    | VarStatement loc (VariableDeclaration iden loc)
    | ReturnStatement loc (Maybe (Expression iden loc))
    | ContinueStatement loc
    | BreakStatement loc
    | ExpressionStatement loc (Expression iden loc)
    | AnnStatement loc [StatementAnnotation iden loc]
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (Statement iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (Statement iden loc)

instance Location loc => Located (Statement iden loc) where
    type (LocOf (Statement iden loc)) = loc
    loc (CompoundStatement l _) = l
    loc (IfStatement l _ _ _) = l
    loc (ForStatement l _ _ _ _ _) = l
    loc (WhileStatement l _ _ _) = l
    loc (PrintStatement l _) = l
    loc (DowhileStatement l _ _ _) = l
    loc (AssertStatement l _) = l
    loc (SyscallStatement l _ _) = l
    loc (VarStatement l _) = l
    loc (ReturnStatement l _) = l
    loc (ContinueStatement l) = l
    loc (BreakStatement l) = l
    loc (ExpressionStatement l _) = l
    loc (AnnStatement l _) = l
    updLoc (CompoundStatement _ x) l = CompoundStatement l x
    updLoc (IfStatement _ x y z) l = IfStatement l x y z
    updLoc (ForStatement _ x y z w s) l = ForStatement l x y z w s
    updLoc (WhileStatement _ x y z) l = WhileStatement l x y z
    updLoc (PrintStatement _ x) l = PrintStatement l x
    updLoc (DowhileStatement _ x y z) l = DowhileStatement l x y z
    updLoc (AssertStatement _ x) l = AssertStatement l x
    updLoc (SyscallStatement _ x y) l = SyscallStatement l x y
    updLoc (VarStatement _ x) l = VarStatement l x
    updLoc (ReturnStatement _ x) l = ReturnStatement l x
    updLoc (ContinueStatement _) l = ContinueStatement l
    updLoc (BreakStatement _) l = BreakStatement l
    updLoc (ExpressionStatement _ x) l = ExpressionStatement l x
    updLoc (AnnStatement _ x) l = AnnStatement l x
 
instance PP m iden => PP m [Statement iden loc] where
    pp [] = return empty
    pp ss = liftM vcat $ mapM pp ss
 
instance PP m iden => PP m (Statement iden loc) where
    pp (CompoundStatement _ ss) = do
        ppss <- pp ss
        return $ lbrace $+$ nest 4 ppss $+$ rbrace
    pp (IfStatement _ e thenS elseS) = do
        ppe <- pp e
        ppthenS <- pp thenS
        ppElseelseS <- ppElse elseS
        return $ text "if" <+> parens ppe <+> ppthenS <+> ppElseelseS
      where
        ppElse Nothing = return empty
        ppElse (Just s) = liftM (text "else" <+>) (pp s)
    pp (ForStatement _ i e1 e2 ann s) = do
        ppi <- pp i
        pp1 <- ppMb e1
        pp2 <- ppMb e2
        ppa <- pp ann
        pps <- pp s
        return $ text "for" <> parens (ppi <> semi <> pp1 <> semi <> pp2) $+$ ppa $+$ pps
    pp (WhileStatement _ e ann s) = do
        ppe <- pp e
        pps <- pp s
        ppa <- pp ann
        return $ text "while" <> parens ppe $+$ ppa $+$ pps
    pp (PrintStatement _ es) = do
        ppes <- pp es
        return $ text "print" <> parens ppes <> semi
    pp (DowhileStatement _ ann s e) = do
        ppe <- pp e
        pp1 <- pp ann
        pp2 <- pp s
        return $ text "do" $+$ pp1 $+$ pp2 <+> text "while" <+> parens ppe <> semi
    pp (AssertStatement _ e) = do
        ppe <- pp e
        return $ text "assert" <> parens ppe <> semi
    pp (SyscallStatement _ n []) = do
        return $ text "__syscall" <> parens (text (show n)) <> semi
    pp (SyscallStatement _ n ps) = do
        pps <- ppSyscallParameters ps
        return $ text "__syscall" <> parens (text (show n) <> comma <+> pps) <> semi
    pp (VarStatement _ vd) = do
        ppvd <- pp vd
        return $ ppvd <> semi
    pp (ReturnStatement _ e) = do
        ppe <- ppMb e
        return $ text "return" <+> ppe <> semi
    pp (ContinueStatement _) = do
        return $ text "continue" <> semi
    pp (BreakStatement _) = do
        return $ text "break" <> semi
    pp (ExpressionStatement _ e) = do
        ppe <- pp e
        return $ ppe <> semi
    pp (AnnStatement _ ann) = pp ann
    
ppSyscallParameters ps = do
    pp1 <- mapM pp ps
    return $ sepBy comma pp1
 
data SyscallParameter iden loc
    = SyscallPush loc (Expression iden loc)
    | SyscallReturn loc (VarName iden loc)
    | SyscallPushRef loc (VarName iden loc)
    | SyscallPushCRef loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (SyscallParameter iden loc)  
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
  
instance PP m iden => PP m (SyscallParameter iden loc) where
    pp (SyscallPush _ e) = pp e
    pp (SyscallReturn _ v) = liftM (text "__return" <+>) $ pp v
    pp (SyscallPushRef _ v) = liftM (text "__ref" <+>) $ pp v
    pp (SyscallPushCRef _ e) = liftM (text "__cref" <+>) $ pp e
  
-- Indices: not strictly expressions as they only appear in specific context

type Subscript iden loc = NeList (Index iden loc)

instance PP m iden => PP m (Subscript iden loc) where
    pp is = do
        ps <- mapM pp is
        return $ brackets (sepBy comma ps)

data Index iden loc
    = IndexSlice loc (Maybe (Expression iden loc)) (Maybe (Expression iden loc))
    | IndexInt loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (Index iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (Index iden loc)

instance Location loc => Located (Index iden loc) where
    type LocOf (Index iden loc) = loc
    loc (IndexSlice l _ _) = l
    loc (IndexInt l _) = l
    updLoc (IndexSlice _ x y) l = IndexSlice l x y
    updLoc (IndexInt _ x) l = IndexInt l x
  
instance PP m iden => PP m (Index iden loc) where
    pp (IndexSlice _ e1 e2) = do
        p1 <- ppMb e1
        p2 <- ppMb e2
        return $ p1 <+> char ':' <+> p2
    pp (IndexInt _ e) = pp e
  
-- Expressions:  

data Quantifier loc
    = ForallQ loc
    | ExistsQ loc
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary loc) => Binary (Quantifier loc)  
instance Hashable loc => Hashable (Quantifier loc)
instance Monad m => PP m (Quantifier loc) where
    pp (ForallQ _) = return $ text "forall"
    pp (ExistsQ _) = return $ text "exists"

instance Location loc => Located (Quantifier loc) where
    type LocOf (Quantifier loc) = loc
    loc (ForallQ l) = l
    loc (ExistsQ l) = l
    updLoc (ForallQ _) l = ForallQ l
    updLoc (ExistsQ _) l = ExistsQ l

data Expression iden loc
    = BinaryAssign loc (Expression iden loc) (BinaryAssignOp loc) (Expression iden loc)
    | QualExpr loc (Expression iden loc) (TypeSpecifier iden loc)
    | CondExpr loc (Expression iden loc) (Expression iden loc) (Expression iden loc)
    | BinaryExpr loc (Expression iden loc) (Op iden loc) (Expression iden loc)
    | UnaryExpr loc (Op iden loc) (Expression iden loc)
    | PreOp loc (Op iden loc) (Expression iden loc)
    | PostOp loc (Op iden loc) (Expression iden loc)
    | DomainIdExpr loc (SecTypeSpecifier iden loc)
    | LeakExpr loc (Expression iden loc)
    | BytesFromStringExpr loc (Expression iden loc)
    | StringFromBytesExpr loc (Expression iden loc)
    | VArraySizeExpr loc (Expression iden loc)
    | ProcCallExpr loc (ProcedureName iden loc) (Maybe [(TemplateTypeArgument iden loc,IsVariadic)]) [(Expression iden loc,IsVariadic)]
    | PostIndexExpr loc (Expression iden loc) (Subscript iden loc)
    | SelectionExpr loc (Expression iden loc) (AttributeName iden loc)
    | RVariablePExpr loc (VarName iden loc)
    | LitPExpr loc (Literal loc)
    | ArrayConstructorPExpr loc [Expression iden loc]
    | MultisetConstructorPExpr loc [Expression iden loc]
    | ResultExpr loc
    | QuantifiedExpr loc (Quantifier loc) [(TypeSpecifier iden loc,VarName iden loc)] (Expression iden loc)
    | BuiltinExpr loc String [Expression iden loc]
    | ToMultisetExpr loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (Expression iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (Expression iden loc)

instance Location loc => Located (Expression iden loc) where
    type LocOf (Expression iden loc) = loc
    loc (BuiltinExpr l _ _) = l
    loc (ToMultisetExpr l _) = l
    loc (MultisetConstructorPExpr l _) = l
    loc (BinaryAssign l _ _ _) = l
    loc (LeakExpr l _) = l
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
    loc (ResultExpr l) = l
    loc (QuantifiedExpr l _ _ _) = l
    updLoc (BuiltinExpr _ n x) l = BuiltinExpr l n x
    updLoc (ToMultisetExpr _ x) l = ToMultisetExpr l x
    updLoc (MultisetConstructorPExpr _ x) l = MultisetConstructorPExpr l x
    updLoc (LeakExpr _ x) l = LeakExpr l x
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
    updLoc (ResultExpr _) l = ResultExpr l
    updLoc (QuantifiedExpr _ x y z) l = QuantifiedExpr l x y z


ppVariadic :: Doc -> IsVariadic -> Doc
ppVariadic x False = x
ppVariadic x True = if PP.isEmpty x then x else x <> text "..."

ppVariadicArg :: Monad m => (a -> m Doc) -> (a,IsVariadic) -> m Doc
ppVariadicArg ppA (e,isVariadic) = do
    pp1 <- ppA e
    return $ ppVariadic pp1 isVariadic
 
instance PP m iden => PP m (Expression iden loc) where
    pp (BuiltinExpr l n e) = do
        ppe <- pp e
        return $ text "__builtin" <> parens (text (show n) <>  char ',' <> ppe)
    pp (ToMultisetExpr l e) = do
        ppe <- pp e
        return $ text "multiset" <> parens ppe
    pp (MultisetConstructorPExpr l es) = do
        ppes <- mapM pp es
        return $ text "multiset" <> braces (sepBy comma ppes)
    pp (BinaryAssign _ post op e) = do
        pp1 <- pp post
        pp2 <- pp op
        pp3 <- pp e
        return $ pp1 <+> pp2 <+> pp3
    pp (QualExpr _ e t) = do
        ppe <- pp e
        ppt <- pp t
        return $ parens (ppe <+> text "::" <+> ppt)
    pp (CondExpr _ lor thenE elseE) = do
        pp1 <- pp lor
        pp2 <- pp thenE
        pp3 <- pp elseE
        return $ pp1 <+> char '?' <+> pp2 <+> char ':' <+> pp3
    pp (BinaryExpr _ e1 o e2) = do
        pp1 <- pp e1
        pp2 <- pp o
        pp3 <- pp e2
        return $ parens (pp1 <+> pp2 <+> pp3)
    pp (PreOp _ (OpAdd _) e) = do
        ppe <- pp e
        return $ text "++" <> ppe
    pp (PreOp _ (OpSub _) e) = do
        ppe <- pp e
        return $ text "--" <> ppe
    pp (PostOp _ (OpAdd _) e) = do
        ppe <- pp e
        return $ ppe <> text "++"
    pp (PostOp _ (OpSub _) e) = do
        ppe <- pp e
        return $ ppe <> text "--"
    pp (UnaryExpr _ o e) = do
        ppo <- pp o
        ppe <- pp e
        return $ ppo <> ppe
    pp (DomainIdExpr _ t) = do
        ppt <- pp t
        return $ text "__domainid" <> parens ppt
    pp (BytesFromStringExpr _ t) = do
        ppt <- pp t
        return $ text "__bytes_from_string" <> parens ppt
    pp (StringFromBytesExpr _ t) = do
        ppt <- pp t
        return $ text "__string_from_bytes" <> parens ppt
    pp (VArraySizeExpr _ e) = do
        ppe <- pp e
        return $ text "size..." <> parens ppe
    pp (ProcCallExpr _ n ts es) = do
        ppn <- pp n
        let f1 ts = do
            pp2 <- mapM (ppVariadicArg pp) ts
            return $ abrackets (sepBy comma pp2)
        pp3 <- mapM (ppVariadicArg pp) es
        pp1 <- ppOpt ts f1
        return $ ppn <> pp1 <> parens (sepBy comma pp3)
    pp (PostIndexExpr _ e s) = do
        ppe <- pp e
        pps <- pp s
        return $ ppe <> pps
    pp (SelectionExpr _ e v) = do
        ppe <- pp e
        ppv <- pp v
        return $ ppe <> char '.' <> ppv
    pp (ArrayConstructorPExpr _ es) = do
        ppes <- mapM pp es
        return $ braces (sepBy comma ppes)
    pp (RVariablePExpr _ v) = pp v
    pp (LitPExpr _ l) = pp l
    pp (ResultExpr l) = return $ text "\\result"
    pp (LeakExpr l e) = do
        ppe <- pp e
        return $ text "leak" <> parens ppe
    pp (QuantifiedExpr l q vs e) = do
        pp1 <- mapM (\(t,v) -> do { p1 <- pp t; p2 <- pp v; return $ p1 <+> p2 }) vs
        pp2 <- pp e
        return $ text "forall" <+> sepBy comma pp1 <+> char ';' <+> pp2
  
data CastType iden loc
    = CastPrim (PrimitiveDatatype loc)
    | CastTy (TypeName iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary iden,Binary loc) => Binary (CastType iden loc)
instance (Hashable iden,Hashable loc) => Hashable (CastType iden loc)

instance Location loc => Located (CastType iden loc) where
    type LocOf (CastType iden loc) = loc
    loc (CastPrim t) = loc t
    loc (CastTy t) = loc t
    updLoc (CastPrim x) l = CastPrim $ updLoc x l
    updLoc (CastTy x) l = CastTy $ updLoc x l

instance PP m iden => PP m (CastType iden loc) where
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
  
instance (Binary loc) => Binary (BinaryAssignOp loc)  
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
  
instance Monad m => PP m (BinaryAssignOp loc) where
    pp (BinaryAssignEqual _) = return $ text "="
    pp (BinaryAssignMul   _) = return $ text "*="
    pp (BinaryAssignDiv   _) = return $ text "/="
    pp (BinaryAssignMod   _) = return $ text "%="
    pp (BinaryAssignAdd   _) = return $ text "+="
    pp (BinaryAssignSub   _) = return $ text "-="
    pp (BinaryAssignAnd   _) = return $ text "&="
    pp (BinaryAssignOr    _) = return $ text "|="
    pp (BinaryAssignXor   _) = return $ text "^="
  
data Literal loc
    = IntLit loc Integer
    | StringLit loc String
    | BoolLit loc Bool
    | FloatLit loc Double
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary loc) => Binary (Literal loc)  
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
  
instance Monad m => PP m (Literal loc) where
    pp (IntLit _ i) = return $ integer i
    pp (StringLit _ s) = return $ text (show s)
    pp (BoolLit _ True) = return $ text "true"
    pp (BoolLit _ False) = return $ text "false"
    pp (FloatLit _ f) = return $ text (show f)

unaryLitExpr :: Expression iden loc -> Expression iden loc
unaryLitExpr (UnaryExpr l (OpSub _) (LitPExpr _ (IntLit l1 i))) = LitPExpr l $ IntLit l1 (-i)
unaryLitExpr (UnaryExpr l (OpSub _) (LitPExpr _ (FloatLit l1 f))) = LitPExpr l $ FloatLit l1 (-f)
unaryLitExpr e = e
    
instance PP m iden => PP m [Expression iden loc] where
    pp xs = do
        pp1 <- mapM pp xs
        return $ parens $ sepBy comma pp1
    
instance PP m iden => PP m [(Expression iden loc, IsVariadic)] where
    pp xs = do
        pp1 <- mapM (ppVariadicArg pp) xs
        return $ parens $ sepBy comma pp1
    
varExpr :: Location loc => VarName iden loc -> Expression iden loc
varExpr v = RVariablePExpr (loc v) v

-- ** Annotations

data GlobalAnnotation iden loc
    = GlobalFunctionAnn loc (FunctionDeclaration iden loc)
    | GlobalStructureAnn loc (StructureDeclaration iden loc)
    | GlobalProcedureAnn loc (ProcedureDeclaration iden loc)
    | GlobalTemplateAnn loc (TemplateDeclaration iden loc)
    | GlobalAxiomAnn loc (AxiomDeclaration iden loc)
    | GlobalLemmaAnn loc (LemmaDeclaration iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (GlobalAnnotation iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (GlobalAnnotation iden loc)

instance Location loc => Located (GlobalAnnotation iden loc) where
    type LocOf (GlobalAnnotation iden loc) = loc
    loc (GlobalFunctionAnn l _)    = l
    loc (GlobalStructureAnn l _) = l
    loc (GlobalProcedureAnn l _) = l
    loc (GlobalTemplateAnn l _)    = l
    loc (GlobalAxiomAnn l _)    = l
    loc (GlobalLemmaAnn l _)    = l
    updLoc (GlobalFunctionAnn _ x)    l = (GlobalFunctionAnn l x)  
    updLoc (GlobalTemplateAnn _ x)    l = (GlobalTemplateAnn l x)  
    updLoc (GlobalStructureAnn _ x)   l = (GlobalStructureAnn l x)
    updLoc (GlobalProcedureAnn _ x)   l = (GlobalProcedureAnn l x)
    updLoc (GlobalAxiomAnn _ x)   l = (GlobalAxiomAnn l x)
    updLoc (GlobalLemmaAnn _ x)   l = (GlobalLemmaAnn l x)

instance PP m iden => PP m (GlobalAnnotation iden loc) where
    pp (GlobalFunctionAnn _ f) = liftM ppAnns $ pp f
    pp (GlobalStructureAnn _ s) = liftM ppAnns $ pp s
    pp (GlobalProcedureAnn _ p) = liftM ppAnns $ pp p
    pp (GlobalTemplateAnn _ t) = liftM ppAnns $ pp t
    pp (GlobalAxiomAnn _ a) = liftM ppAnns $ pp a
    pp (GlobalLemmaAnn _ a) = liftM ppAnns $ pp a

instance PP m iden => PP m [GlobalAnnotation iden loc] where
    pp xs = liftM vcat $ mapM pp xs

data ProcedureAnnotation iden loc
    = RequiresAnn loc Bool Bool (Expression iden loc)
    | EnsuresAnn loc Bool Bool (Expression iden loc)
    | InlineAnn loc Bool
    | PDecreasesAnn loc (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (ProcedureAnnotation iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (ProcedureAnnotation iden loc)

instance Location loc => Located (ProcedureAnnotation iden loc) where
    type LocOf (ProcedureAnnotation iden loc) = loc
    loc (RequiresAnn l _ _ _)    = l
    loc (PDecreasesAnn l e) = l
    loc (EnsuresAnn l _ _ _) = l
    loc (InlineAnn l b) = l
    updLoc (RequiresAnn _ isFree isLeak x)    l = (RequiresAnn l isFree isLeak x)   
    updLoc (EnsuresAnn _ isFree isLeak x)    l = (EnsuresAnn l isFree isLeak x)   
    updLoc (InlineAnn _ b) l = InlineAnn l b
    updLoc (PDecreasesAnn _ e) l = PDecreasesAnn l e

instance PP m iden => PP m (ProcedureAnnotation iden loc) where
    pp (RequiresAnn _ isFree isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree isFree $ ppLeak isLeak $ text "requires" <+> ppe <> semicolon
    pp (PDecreasesAnn l e) = do
        ppe <- pp e
        return $ ppAnn $ text "decreases" <+> ppe <> semicolon
    pp (EnsuresAnn _ isFree isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree isFree $ ppLeak isLeak $ text "ensures" <+> ppe <> semicolon
    pp (InlineAnn _ True) = return $ ppAnn $ text "inline" <> semicolon
    pp (InlineAnn _ False) = return $ ppAnn $ text "noinline" <> semicolon

ppFree isFree doc = if isFree then text "free" <+> doc else doc
ppLeak isLeak doc = if isLeak then text "leakage" <+> doc else doc

instance PP m iden => PP m [ProcedureAnnotation iden loc] where
    pp xs = liftM vcat $ mapM pp xs

data LoopAnnotation iden loc
    = DecreasesAnn loc Bool (Expression iden loc)
    | InvariantAnn loc Bool Bool (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)
  
instance (Binary iden,Binary loc) => Binary (LoopAnnotation iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (LoopAnnotation iden loc)

instance Location loc => Located (LoopAnnotation iden loc) where
    type LocOf (LoopAnnotation iden loc) = loc
    loc (DecreasesAnn l _ _)    = l
    loc (InvariantAnn l _ _ _) = l
    updLoc (DecreasesAnn _ isFree x)    l = (DecreasesAnn l isFree x)   
    updLoc (InvariantAnn _ isFree isLeak x)    l = (InvariantAnn l isFree isLeak x)   

instance PP m iden => PP m (LoopAnnotation iden loc) where
    pp (DecreasesAnn _ free e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree free $ text "decreases" <+> ppe <> semicolon
    pp (InvariantAnn _ free isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppFree free $ ppLeak isLeak $ text "invariant" <+> ppe <> semicolon
    
instance PP m iden => PP m [LoopAnnotation iden loc] where
    pp xs = liftM vcat $ mapM pp xs

data StatementAnnotation iden loc
    = AssumeAnn loc Bool (Expression iden loc)
    | AssertAnn loc Bool (Expression iden loc)
    | EmbedAnn loc Bool (Statement iden loc)
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord,Generic)

instance (Binary iden,Binary loc) => Binary (StatementAnnotation iden loc)  
instance (Hashable iden,Hashable loc) => Hashable (StatementAnnotation iden loc)

instance Location loc => Located (StatementAnnotation iden loc) where
    type LocOf (StatementAnnotation iden loc) = loc
    loc (AssumeAnn l _ _)    = l
    loc (AssertAnn l _ _) = l
    loc (EmbedAnn l isLeak e) = l
    updLoc (EmbedAnn _ isLeak e) l = EmbedAnn l isLeak e
    updLoc (AssumeAnn _ isLeak x)    l = (AssumeAnn l isLeak x)   
    updLoc (AssertAnn _ isLeak x)    l = (AssertAnn l isLeak x)   

instance PP m iden => PP m (StatementAnnotation iden loc) where
    pp (AssumeAnn _ isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppLeak isLeak $ text "assume" <+> ppe <> semicolon
    pp (AssertAnn _ isLeak e) = do
        ppe <- pp e
        return $ ppAnn $ ppLeak isLeak $ text "assert" <+> ppe <> semicolon
    pp (EmbedAnn l isLeak s) = do
        pps <- pp s
        return $ ppAnns $ ppLeak isLeak pps

instance PP m iden => PP m [StatementAnnotation iden loc] where
    pp xs = liftM vcat $ mapM pp xs

ppAnns doc = vcat $ map (\x -> text "//@" <+> text x) $ lines $ show doc
ppAnn doc = text "//@" <+> doc

hasResult :: (Data iden,Data loc) => Expression iden loc -> Bool
hasResult (x::Expression iden loc) = everything (||) (mkQ False $ res (Proxy::Proxy iden) (Proxy::Proxy loc)) x
    where
    res :: Proxy iden -> Proxy loc -> Expression iden loc -> Bool
    res _ _ (ResultExpr _) = True
    res _ _ x = False

$(deriveBifunctor ''Module)
$(deriveBifunctor ''CastType)
$(deriveBifunctor ''AttributeName)
$(deriveBifunctor ''ModuleName)
$(deriveBifunctor ''TemplateArgName)
$(deriveBifunctor ''Program)
$(deriveBifunctor ''ImportDeclaration)
$(deriveBifunctor ''GlobalDeclaration)
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
$(deriveBifunctor ''Op) 
$(deriveBifunctor ''Expression) 
$(deriveBifunctor ''GlobalAnnotation) 
$(deriveBifunctor ''LemmaDeclaration) 
$(deriveBifunctor ''AxiomDeclaration) 
$(deriveBifunctor ''FunctionDeclaration) 
$(deriveBifunctor ''ProcedureAnnotation) 
$(deriveBifunctor ''LoopAnnotation) 
$(deriveBifunctor ''StatementAnnotation) 









