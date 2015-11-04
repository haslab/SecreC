{-# LANGUAGE StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars
import Language.SecreC.Parser.Parsec

import Data.Maybe
import Data.Monoid
import Data.Generics hiding (GT)
import Data.Dynamic
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Control.Monad.State as State
import Control.Monad.Reader
import Control.Monad.Trans.RWS (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS as RWS
import Control.Monad.Except

import System.IO.Unsafe
import Unsafe.Coerce

-- warn for unused local variables

data Scope = GlobalScope | LocalScope
  deriving (Show,Read,Data,Typeable)

data TcEnv loc = TcEnv {
      globalVars :: Map Identifier (EntryEnv loc) -- ^ global variables: name |-> type of the variable
    , localVars  :: Map Identifier (EntryEnv loc) -- ^ local variables: name |-> type of the variable
    , kinds :: Map Identifier (EntryEnv loc) -- ^ defined kinds: name |-> type of the kind
    , domains :: Map Identifier (EntryEnv loc) -- ^ defined domains: name |-> type of the domain
    -- a list of overloaded operators; akin to Haskell type class operations
    -- we don't allow specialization of function templates
    , operators :: Map (Op ()) (Map Position (EntryEnv loc)) -- ^ defined operators: name |-> procedure decl
    -- a list of overloaded procedures; akin to Haskell type class operations
    -- we don't allow specialization of function templates
    , procedures :: Map Identifier (Map Position (EntryEnv loc)) -- ^ defined procedures: name |-> procedure decl
    -- | a base template and a list of specializations; akin to Haskell type functions
    , structs :: Map Identifier (EntryEnv loc,Map Position (EntryEnv loc)) -- ^ defined structs: name |-> struct decl
    , inTemplate :: Bool -- ^ @True@ if we are type checking the body of a template declaration
    , templateConstraints :: TDict -- a dictionary with a set of inferred constraints and resolved constraints
    , tyVarId :: TyVarId
    }
  deriving Functor

vars env = Map.union (localVars env) (globalVars env)

insideTemplate :: TcM loc Bool
insideTemplate = liftM inTemplate State.get

resetLocal :: TcEnv loc -> TcEnv loc
resetLocal e = e { localVars = Map.empty, templateConstraints = mempty }

emptyTcEnv :: TcEnv loc
emptyTcEnv = TcEnv Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty False mempty 0

data EntryEnv loc = EntryEnv {
      entryLoc :: loc -- ^ Location where the entry is defined
    , entryType :: Type -- ^ Type of the entry
    }
  deriving Functor

instance Location loc => Located (EntryEnv loc) where
    type LocOf (EntryEnv loc) = loc
    loc = entryLoc

-- | Gets the variables of a given type class
getVars :: Location loc => Scope -> TypeClass -> TcReaderM loc (Map Identifier (EntryEnv loc))
getVars GlobalScope c = do
    vs <- liftM globalVars ask
    return $ Map.filter (\e -> typeClass (entryType e) == c) vs
getVars LocalScope c = do
    vs <- liftM vars ask
    return $ Map.filter (\e -> typeClass (entryType e) == c) vs

addVar :: Location loc => Scope -> Identifier -> EntryEnv loc -> TcM loc ()
addVar GlobalScope n e = modify $ \env -> env { globalVars = Map.insert n e (globalVars env) }
addVar LocalScope n e = modify $ \env -> env { localVars = Map.insert n e (localVars env) }

checkVariable :: Location loc => Scope -> VarName loc -> TcReaderM loc Type
checkVariable scope (VarName l n) = do
    vs <- getVars scope TypeC
    case Map.lookup n vs of
        Just e -> return $ entryType e
        Nothing -> tcError (locpos l) $ VariableNotFound n

-- | Adds a new variable to the environment
newVariable :: Location loc => Scope -> VarName (Typed loc) -> TcM loc ()
newVariable scope (VarName (Typed l t) n) = do
    vars <- tcReaderM $ getVars scope TypeC
    case Map.lookup n vars of
        Just e -> tcWarn (locpos l) $ ShadowedVariable n (locpos $ entryLoc e)
        Nothing -> addVar scope n (EntryEnv l t)

-- | Adds a new domain variable to the environment
newDomainVariable :: Location loc => Scope -> DomainName (Typed loc) -> TcM loc ()
newDomainVariable scope (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ InvalidDomainVariableName n (locpos $ entryLoc e)
        Nothing -> do
            vars <- tcReaderM $ getVars scope DomainC
            case Map.lookup n vars of
                Just e -> tcWarn (locpos l) $ ShadowedVariable n (locpos $ entryLoc e)
                Nothing -> addVar scope n (EntryEnv l t)

-- | Adds a new type variable to the environment
newTypeVariable :: Location loc => Scope -> TypeName (Typed loc) -> TcM loc ()
newTypeVariable scope (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (b,es) -> tcError (locpos l) $ InvalidTypeVariableName n (map (locpos . entryLoc) (b:Map.elems es))
        Nothing -> do
            vars <- tcReaderM $ getVars scope TypeStarC
            case Map.lookup n vars of
                Just e -> tcWarn (locpos l) $ ShadowedVariable n (locpos $ entryLoc e)
                Nothing -> addVar scope n (EntryEnv l t)

-- | Adds a new domain to the environment
newDomain :: Location loc => DomainName (Typed loc) -> TcM loc ()
newDomain (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ MultipleDefinedDomain n (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t
            modify $ \env -> env { domains = Map.insert n e (domains env) }

-- | Checks if a domain exists in scope, and returns its type
-- Searches for both user-defined private domains and domain variables
checkPrivateDomain :: Location loc => DomainName loc -> TcReaderM loc Type
checkPrivateDomain (DomainName l n) = do
    ds <- liftM domains ask
    case Map.lookup n ds of
        Just e -> return $ entryType e
        Nothing -> do
            dvars <- getVars LocalScope DomainC
            case Map.lookup n dvars of
                Just e -> return $ entryType e
                Nothing -> tcError (locpos l) $ NotDefinedDomain n
    
-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: Location loc => TypeName loc -> TcReaderM loc [EntryEnv loc]
checkType (TypeName l n) = do
    ss <- liftM structs ask
    case Map.lookup n ss of
        Just (base,es) -> return (base : Map.elems es)
        Nothing -> do
            vars <- getVars LocalScope TypeStarC
            case Map.lookup n vars of
                Just e -> return [ e { entryType = TVar (Typed (Left n) $ entryType e) } ] -- return the type variable
                Nothing -> tcError (locpos l) $ NotDefinedType n

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkNonTemplateType :: Location loc => TypeName loc -> TcReaderM loc Type
checkNonTemplateType tn@(TypeName l n) = do
    es <- checkType tn
    case es of
        [e] -> return $ entryType e 
        es -> tcError (locpos l) $ NoNonTemplateType n

-- | Checks if a template type exists in scope
-- Returns all template type declarations in scope, base template first
checkTemplateType :: Location loc => TypeName loc -> TcReaderM loc [EntryEnv loc]
checkTemplateType ty = do
    es <- checkType ty
    let check e = case entryType e of
                    TType {} -> return ()
                    otherwise -> tcError (locpos $ loc ty) $ NoTemplateType (fmap locpos $ ty) (locpos $ entryLoc e)
    mapM_ check es
    return es

-- | Checks if a variable argument of a template exists in scope
-- The argument can be a (user-defined or variable) type, a (user-defined or variable) domain or a dimension variable
checkTemplateArg :: Location loc => TemplateArgName loc -> TcReaderM loc Type
checkTemplateArg (TemplateArgName l n) = do
    env <- ask
    let ss = structs env
    let ds = domains env
    let vs = vars env
    case (Map.lookup n ss,Map.lookup n ds,Map.lookup n vs) of
        (Just (base,es),Nothing,Nothing) -> case (base:Map.elems es) of
            [e] -> case entryType e of
                TpltType {} -> tcError (locpos l) $ NoNonTemplateType n
                t -> return t
            es -> tcError (locpos l) $ NoNonTemplateType n
        (Nothing,Just e,Nothing) -> return $ entryType e
        (Nothing,Nothing,Just e) -> return $ entryType e
        (mb1,mb2,mb3) -> tcError (locpos l) $ AmbiguousName n $ map (locpos . entryLoc) $ maybe [] (\(b,es) -> b:Map.elems es) mb1 ++ maybeToList mb2 ++ maybeToList mb3

-- | Checks that a kind exists in scope
checkKind :: Location loc => KindName loc -> TcReaderM loc ()
checkKind (KindName l n) = do
    ks <- liftM kinds ask
    case Map.lookup n ks of
        Just e -> return ()
        Nothing -> tcError (locpos l) $ NotDefinedKind n

-- | Adds a new kind to the environment
newKind :: Location loc => KindName (Typed loc) -> TcM loc ()
newKind (KindName (Typed l t) n) = do
    ks <- liftM kinds get
    case Map.lookup n ks of
        Just e -> tcError (locpos l) $ MultipleDefinedKind n (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t
            modify $ \env -> env { kinds = Map.insert n e (kinds env) } 

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: Location loc => [Typed VarIdentifier] -> Op (Typed loc) -> TcM loc ()
addTemplateOperator vars op = do
    let Typed l t = loc op
    let o = fmap (const ()) op
    cstrs <- liftM templateConstraints get
    i <- newTyVarId
    let e = EntryEnv l (TpltType i vars cstrs [] t)
    modify $ \env -> env { operators = Map.alter (Just . Map.insert (locpos l) e . maybe Map.empty id) o (operators env) }

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: Location loc => Op (Typed loc) -> TcM loc ()
newOperator op = do
    let Typed l t = loc op
    let o = fmap (const ()) op
    let e = EntryEnv l t
    modify $ \env -> env { operators = Map.alter (Just . Map.insert (locpos l) e . maybe Map.empty id) o (operators env) }
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: Location loc => [Typed VarIdentifier] -> ProcedureName (Typed loc) -> TcM loc ()
addTemplateProcedure vars (ProcedureName (Typed l t) n) = do
    cstrs <- liftM templateConstraints get
    i <- newTyVarId
    let e = EntryEnv l (TpltType i vars cstrs [] t)
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert (locpos l) e . maybe Map.empty id) n (procedures env) }

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: Location loc => ProcedureName (Typed loc) -> TcM loc ()
newProcedure (ProcedureName (Typed l t) n) = do
    let e = EntryEnv l t
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert (locpos l) e . maybe Map.empty id) n (procedures env) }
  
 -- | Checks that a procedure exists.
checkProcedure :: Location loc => ProcedureName loc -> TcReaderM loc [EntryEnv loc]
checkProcedure (ProcedureName l n) = do
    ps <- liftM procedures ask
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ NotDefinedProcedure n
        Just es -> return $ Map.elems es
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: Location loc => [Typed VarIdentifier] -> TypeName (Typed loc) -> TcM loc ()
addTemplateStruct vars (TypeName (Typed l struct) n) = do
    cstrs <- liftM templateConstraints get
    i <- newTyVarId
    let e = EntryEnv l $ TpltType i vars cstrs [] struct
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate n (locpos $ loc base)
        Nothing -> modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: Location loc => [Typed VarIdentifier] -> [Type] -> TypeName (Typed loc) -> TcM loc ()
addTemplateStructSpecialization vars specials (TypeName (Typed l struct) n) = do
    cstrs <- liftM templateConstraints get
    i <- newTyVarId
    let e = EntryEnv l $ TpltType i vars cstrs specials struct
    let mergeStructs (b1,s1) (b2,s2) = (b2,s1 `Map.union` s2)
    modify $ \env -> env { structs = Map.update (\(b,s) -> Just (b,Map.insert (locpos l) e s)) n (structs env) }

-- | Defines a new struct type
newStruct :: Location loc => TypeName (Typed loc) -> TcM loc ()
newStruct (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStruct n (locpos $ entryLoc base)
        Nothing -> do
            let e = EntryEnv l t
            modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }

type TcM loc = StateT (TcEnv loc) SecrecM

type TcReaderM loc = ReaderT (TcEnv loc) SecrecM

type TcProofM loc = StateT (Substs Type) (TcM loc)

tcProofM :: TcProofM loc a -> TcM loc (a,Substs Type)
tcProofM m = runStateT m (emptySubsts (Proxy::Proxy Type))

addSubstM :: [(Typed VarIdentifier,Type)] -> TcProofM loc ()
addSubstM xs = modify $ \s -> appendSubsts proxy s (substFromList proxy xs)
    where proxy = Proxy :: Proxy Type

tcReaderM :: TcReaderM loc a -> TcM loc a
tcReaderM r = do
    s <- get
    lift $ runReaderT r s

-- | Map different locations over @TcM@ monad.
tcLocM :: (loc2 -> loc1) -> (loc1 -> loc2) -> TcM loc1 a -> TcM loc2 a
tcLocM f g m = do
    s2 <- get
    (x,s1) <- lift $ runStateT m (fmap f s2)
    put (fmap g s1)
    return x

-- | Enters a template declaration
tcTemplateBlock :: TcM loc a -> TcM loc a
tcTemplateBlock m = do
    State.modify (\env -> env { inTemplate = True, templateConstraints = mempty })
    x <- m
    State.modify (\env -> env { inTemplate = False, templateConstraints = mempty })
    return x

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: TcM loc a -> TcM loc a
tcBlock m = do
    s <- get
    lift $ evalStateT m s

tcGlobal :: TcM loc a -> TcM loc a
tcGlobal m = do
    x <- m
    modify resetLocal
    return x

runTcM :: TcM loc a -> SecrecM a
runTcM m = evalStateT m emptyTcEnv

-- | A template constraint with a result type
data TCstr
    = TApp Identifier [Type] -- ^ type template application
    | TDec Identifier [Type] -- ^ type template declaration
    | PApp Identifier [Type] (Maybe Type) -- ^ procedure template application (optional return type)
    | PDec Identifier [Type] (Maybe Type) -- ^ procedure template declaration (optional return type)
    | SupportedOp (Op ()) Type -- ^ operation supported over given type
    | Coerces Type Type -- ^ types coercible
    | Coerces2 Type Type -- ^ bidirectional coercion
    | Declassify Type -- ^ declassification
    | SupportedSize Type -- ^ can call size on the argument type
    | SupportedToString Type -- ^ can call tostring on the argument type
    | ProjectStruct Type (AttributeName ()) -- ^ struct type projection
    | ProjectMatrix Type [(Maybe Integer,Maybe Integer)] -- ^ matrix type projection
    | Cast Type Type -- ^ explicit type cast
  deriving (Data,Typeable,Show,Eq,Ord)
    
instance Vars TCstr where
    type VarOf TCstr = Typed VarIdentifier
    fvs (TApp n args) = fvsFoldable args
    fvs (TDec n args) = fvsFoldable args
    fvs (PApp n args r) = fvsFoldable args `Set.union` fvsFoldable r
    fvs (PDec n args r) = fvsFoldable args `Set.union` fvsFoldable r
    fvs (Coerces x y) = fvs x `Set.union` fvs y
    fvs (Coerces2 x y) = fvs x `Set.union` fvs y
    fvs (Declassify x) = fvs x
    fvs (SupportedSize x) = fvs x
    fvs (SupportedToString x) = fvs x
    fvs (ProjectStruct x _) = fvs x
    fvs (ProjectMatrix t _) = fvs t
    bvs (TApp n args) = bvsFoldable args
    bvs (TDec n args) = bvsFoldable args
    bvs (PApp n args r) = bvsFoldable args `Set.union` bvsFoldable r
    bvs (PDec n args r) = bvsFoldable args `Set.union` bvsFoldable r
    bvs (Coerces x y) = bvs x `Set.union` bvs y
    bvs (Coerces2 x y) = bvs x `Set.union` bvs y
    bvs (Declassify x) = bvs x
    bvs (SupportedSize x) = bvs x
    bvs (SupportedToString x) = bvs x
    bvs (ProjectStruct x _) = bvs x
    bvs (ProjectMatrix t rs) = bvs t

instance Subst TCstr where
    type SubstOf TCstr = Type
    subst f (TApp n args) = TApp n (substTraversable f args)
    subst f (TDec n args) = TDec n (substTraversable f args)
    subst f (PApp n args r) = PApp n (substTraversable f args) (substTraversable f r)
    subst f (PDec n args r) = PDec n (substTraversable f args) (substTraversable f r)
    subst f (Coerces x y) = Coerces (subst f x) (subst f y)
    subst f (Coerces2 x y) = Coerces2 (subst f x) (subst f y)
    subst f (Declassify x) = Declassify (subst f x)
    subst f (SupportedSize x) = SupportedSize (subst f x)
    subst f (SupportedToString x) = SupportedToString (subst f x)
    subst f (ProjectStruct x a) = ProjectStruct (subst f x) a
    subst f (ProjectMatrix x a) = ProjectMatrix (subst f x) a

-- | Template constraint dictionary: Mappings from keys @TCstr t@ to values @t@
data TDict = TDict { unTDict :: Map TCstr (Maybe Type) }
  deriving (Typeable,Eq,Ord,Show,Data)

insertTDict :: TCstr -> Maybe Type -> TDict -> TDict
insertTDict cstr t (TDict dict) = TDict $ Map.insertWith join cstr t dict
    where join x y = maybe y Just x

deleteTDict :: TCstr -> TDict -> TDict
deleteTDict cstr (TDict dict) = TDict $ Map.delete cstr dict

-- | Adds a new template constraint to the environment
addTemplateConstraint :: TCstr -> Maybe Type -> TcM loc ()
addTemplateConstraint cstr res = modify $ \env -> env { templateConstraints = insertTDict cstr res (templateConstraints env) }

remTemplateConstraint :: TCstr -> TcM loc ()
remTemplateConstraint cstr = modify $ \env -> env { templateConstraints = deleteTDict cstr (templateConstraints env) }

instance Monoid TDict where
    mempty = TDict Map.empty
    mappend (TDict xs) (TDict ys) = TDict $ Map.unionWith join xs ys
        where join x y = maybe y Just x

instance Vars TDict where
    type VarOf TDict = Typed VarIdentifier
    fvs (TDict m) = fvsFoldable (Map.keys m) `Set.union` (Set.unions $ map fvsFoldable $ Map.elems m)
    bvs (TDict m) = bvsFoldable (Map.keys m) `Set.union` (Set.unions $ map bvsFoldable $ Map.elems m)

instance Subst TDict where
    type SubstOf TDict = Type
    subst s (TDict m) = TDict $ Map.foldrWithKey (\cstr mb d -> Map.insertWith join (subst s cstr) (fmap (subst s) mb) d) Map.empty m
        where join x y = maybe y Just x

type TyVarId = Int

newTyVarId :: TcM loc TyVarId
newTyVarId = do
    i <- liftM tyVarId get
    modify $ \env -> env { tyVarId = succ (tyVarId env) }
    return i
    
newTyVar :: TcM loc Type
newTyVar = do
    i <- newTyVarId
    return $ TVar (Typed (Right i) TType)

type VarIdentifier = Either Identifier TyVarId

-- | Checks if a type contains any type variables
hasTypeVars :: Type -> Bool
hasTypeVars = everything (&&) (mkQ False q)
    where
    q :: Type -> Bool
    q (TVar _) = True
    q t = False

data Type
    = NoType -- ^ For locations with no associated type information
    | ProcType -- ^ procedure type
        TyVarId -- ^ unique procedure declaration id
        Position -- ^ location of the procedure declaration
        [VarName Type] -- typed procedure arguments
        Type -- return type
    | StructType -- ^ Struct type
            TyVarId -- ^ unique structure declaration id
            Position -- ^ location of the procedure declaration
            [Attribute Type] -- ^ typed arguments
    | TK -- ^ the result of resolving a constraint
        TCstr -- ^ a constraint returning a type
    | TpltType -- ^ Template type
            TyVarId -- ^ unique template declaration id
            [Typed VarIdentifier] -- ^ template variables
            TDict -- ^ template constraints depending on the variables
            [Type] -- ^ template specializations
            Type -- ^ template's type
    | TVar -- ^ type variable
        (Typed VarIdentifier) -- ^ typed variable name
    | TyLit -- ^ the most concrete type for a literal
        (Literal ()) -- ^ the literal itself
    | TDim Integer -- constant dimension
    | TType -- ^ Type of types
    | KType -- ^ Type of kinds
    | DType -- ^ Type of domains
        (Maybe Identifier) -- ^ optional kind of the domain
    | Void -- ^ Empty type
    | StmtType (Set StmtClass) -- ^ Type of a @Statement@
    | CType -- ^ Compound SecreC type
        Type -- ^ security type
        Type -- ^ data type
        (Expression ()) -- ^ dimension (default = 0, i.e., scalars)
        [Expression ()] -- ^ sizes for each dimension (dependent types?) -- NOTE: check bounds if size is statically known?
    | PrimType (PrimitiveDatatype ())
    | Public -- ^ public domain
    | Private -- ^ private domain
        Identifier -- ^ domain
        Identifier -- ^ kind
    | SysPush Type
    | SysRet Type
    | SysRef Type
    | SysCRef Type
  deriving (Show,Data,Typeable,Eq,Ord)

data TypeClass
    = KindStarC -- type of kinds
    | KindC -- kinds
    | DomainC -- for typed domains
    | TypeStarC -- type of types
    | TypeC -- regular type
    | DimC -- dimension type
    | SysC -- system call parameters
  deriving (Read,Show,Data,Typeable,Eq,Ord)

typeClass :: Type -> TypeClass
typeClass TType = TypeStarC
typeClass KType = KindStarC
typeClass (DType _) = KindC
typeClass Public = DomainC
typeClass (Private _ _) = DomainC
typeClass (TDim i) = DimC
typeClass (TVar (Typed v t)) | typeClass t == KindC = DomainC -- domain variables
                             | typeClass t == TypeStarC = TypeC -- type variables
                             | isIntType t = DimC -- dimension variables
typeClass (SysPush _) = SysC
typeClass (SysRet _) = SysC
typeClass (SysRef _) = SysC
typeClass (SysCRef _) = SysC
typeClass _ = TypeC

isBoolType :: Type -> Bool
isBoolType (PrimType (DatatypeBool _)) = True
isBoolType _ = False

isIntType :: Type -> Bool
isIntType (TyLit (IntLit _ i)) = True
isIntType (PrimType p) = isIntPrimType p
isIntType t = False

isIntPrimType :: PrimitiveDatatype () -> Bool
isIntPrimType (DatatypeInt _) = True
isIntPrimType (DatatypeUint   _) = True
isIntPrimType (DatatypeInt8   _) = True
isIntPrimType (DatatypeUint8  _) = True
isIntPrimType (DatatypeInt16  _) = True
isIntPrimType (DatatypeUint16 _) = True
isIntPrimType (DatatypeInt32  _) = True
isIntPrimType (DatatypeUint32 _) = True
isIntPrimType (DatatypeInt64  _) = True
isIntPrimType (DatatypeUint64 _) = True
isIntPrimType (DatatypeXorUint8   _) = True
isIntPrimType (DatatypeXorUint16  _) = True
isIntPrimType (DatatypeXorUint32  _) = True
isIntPrimType (DatatypeXorUint64  _) = True
isIntPrimType (DatatypeXorUint    _) = True
isIntPrimType t = False

isFloatType :: Type -> Bool
isFloatType (TyLit (FloatLit _ f)) = True
isFloatType (PrimType p) = isFloatPrimType p
isFloatType t = False

isFloatPrimType :: PrimitiveDatatype () -> Bool
isFloatPrimType (DatatypeFloat _) = True
isFloatPrimType (DatatypeFloat32   _) = True
isFloatPrimType (DatatypeFloat64   _) = True
isFloatPrimType t = False

isNumericType :: Type -> Bool
isNumericType t = isIntType t || isFloatType t
  
typedScVar :: ScVar Type -> Typed VarIdentifier
typedScVar (ScVar t i) = Typed (Left i) t

instance Vars Type where
    type VarOf Type = Typed VarIdentifier
    fvs NoType = Set.empty
    fvs (ProcType i p vs t) = fvsFoldable (map (\(VarName l _) -> l) vs) `Set.union` fvs t
    fvs (StructType i p as) = Set.map typedScVar $ fvsFoldable as
    fvs (TK k) = fvs k
    fvs (TpltType i vs cs ss t) = (fvs cs `Set.union` fvsFoldable ss `Set.union` fvs t) `Set.difference` (Set.fromList vs)
    fvs (TVar v) = Set.singleton v
    fvs (TyLit l) = Set.empty
    fvs (TDim i) = Set.empty
    fvs TType = Set.empty
    fvs KType = Set.empty
    fvs (DType _) = Set.empty
    fvs Void = Set.empty
    fvs (StmtType _) = Set.empty
    fvs (CType s d _ _) = fvs s `Set.union` fvs d
    fvs (PrimType _) = Set.empty
    fvs Public = Set.empty
    fvs (Private _ _) = Set.empty
    fvs (SysPush t) = fvs t
    fvs (SysRet t) = fvs t
    fvs (SysRef t) = fvs t
    fvs (SysCRef t) = fvs t
    bvs NoType = Set.empty
    bvs (ProcType i p vs t) = bvsFoldable (map (\(VarName l _) -> l) vs) `Set.union` bvs t
    bvs (StructType i p as) = Set.map typedScVar $ bvsFoldable as
    bvs (TK k) = bvs k
    bvs (TpltType i vs cs ss t) = Set.fromList vs `Set.union` bvs cs `Set.union` bvsFoldable ss `Set.union` bvs t
    bvs (TVar v) = Set.empty
    bvs (TyLit l) = Set.empty
    bvs (TDim i) = Set.empty
    bvs TType = Set.empty
    bvs KType = Set.empty
    bvs (DType _) = Set.empty
    bvs Void = Set.empty
    bvs (StmtType _) = Set.empty
    bvs (CType s d _ _) = bvs s `Set.union` bvs d
    bvs (PrimType _) = Set.empty
    bvs Public = Set.empty
    bvs (Private _ _) = Set.empty
    bvs (SysPush t) = bvs t
    bvs (SysRet t) = bvs t
    bvs (SysRef t) = bvs t
    bvs (SysCRef t) = bvs t

instance Subst Type where
    type SubstOf Type = Type
    subst f NoType = NoType
    subst f (ProcType i p vs t) = ProcType i p (map (fmap (subst f)) vs) (subst f t)
    subst f (StructType i p as) = StructType i p $ map (fmap (subst f)) as
    subst f (TK k) = TK (subst f k)
    subst f (TpltType i vs cs ss t) = TpltType i (map (mapTyped (subst g)) vs) (subst g cs) (map (subst g) ss) (subst g t)
        -- we don't substitute the template's variables, that may shadow the substitution variables
        where g v = if List.elem (unTyped v) (map unTyped vs) then Nothing else f v
    subst f (TVar v) = case f v of
        Nothing -> TVar v
        Just t -> t
    subst f (TyLit l) = TyLit l
    subst f (TDim i) = TDim i
    subst f TType = TType
    subst f KType = KType
    subst f (DType i) = DType i
    subst f Void = Void
    subst f (StmtType s) = StmtType s
    subst f (CType s t d sz) = CType (subst f s) (subst f t) d sz
    subst f (PrimType t) = PrimType t
    subst f Public = Public
    subst f (Private d k) = Private d k
    subst f (SysPush t) = SysPush $ subst f t
    subst f (SysRet t) = SysRet $ subst f t
    subst f (SysRef t) = SysRef $ subst f t
    subst f (SysCRef t) = SysCRef $ subst f t
        
-- | Update the size of a compound type
refineTypeSizes :: Type -> Maybe (Sizes loc) -> Type
refineTypeSizes (CType s t d sz) Nothing = CType s t d []
refineTypeSizes (CType s t d sz) (Just ss) = let Sizes sz' = fmap (const ()) ss in CType s t d $ Foldable.toList sz'
refineTypeSizes _ _ = error "no size"

typeBase :: Type -> Type
typeBase (CType _ b _ _) = b
typeBase _ = error "no base"

data StmtClass
    -- | The execution of the statement may end because of reaching a return statement
    = StmtReturn
    -- | The execution of the statement may end because of reaching a break statement
    | StmtBreak
    -- | The execution of the statement may end because of reaching a continue statement
    | StmtContinue
    -- | The execution of the statement may end without reaching a return, break or continue statement
    | StmtFallthru
  deriving (Read,Show,Data,Typeable,Eq,Ord)

isReturnStmtType :: Type -> Bool
isReturnStmtType (StmtType cs) = cs == Set.singleton StmtReturn

isLoopStmtClass :: StmtClass -> Bool
isLoopStmtClass c = List.elem c [StmtBreak,StmtContinue]

isLoopBreakStmtClass :: StmtClass -> Bool
isLoopBreakStmtClass StmtBreak = True
isLoopBreakStmtClass (StmtReturn) = True
isLoopBreakStmtClass _ = False

isIterationStmtClass :: StmtClass -> Bool
isIterationStmtClass c = List.elem c [StmtContinue,StmtFallthru]

data Typed a = Typed a Type
  deriving (Show,Data,Typeable,Functor,Eq,Ord)

mapTyped :: (Type -> Type) -> Typed a -> Typed a
mapTyped f (Typed a t) = Typed a (f t)

instance Located loc => Located (Typed loc) where
    type (LocOf (Typed loc)) = LocOf loc
    loc = loc . unTyped
    
instance Location a => Location (Typed a) where
    locpos = locpos . unTyped
    noloc = Typed noloc NoType

notTyped :: a -> Typed a
notTyped x = Typed x NoType

typed :: Typed a -> Type
typed (Typed _ t) = t

unTyped :: Typed a -> a
unTyped (Typed a t) = a

locType :: Typed Position -> Type
locType (Typed _ t) = t

typeLoc :: Type -> Position -> Typed Position
typeLoc t l = Typed l t

noTypeLoc :: Loc loc a -> Loc (Typed loc) a
noTypeLoc = mapLoc (flip Typed NoType)

defCType :: Type -> Type
defCType t = CType Public t (integerExpr 0) []

-- | constant integer literal
integerExpr :: Integer -> Expression ()
integerExpr i = fmap (const ()) $ unsafePerformIO $ parseSecreCIOWith defaultOptions "" (show i) scExpression

-- integer types
primIntBounds :: PrimitiveDatatype () -> (Integer,Integer)
primIntBounds (DatatypeInt8 _) = (-128,127)
primIntBounds (DatatypeInt16 _) = (-32768,32767)
primIntBounds (DatatypeInt32 _) = (-2147483648,2147483647)
primIntBounds (DatatypeInt64 _) = (-9223372036854775808,9223372036854775807)
primIntBounds (DatatypeInt _) = (-9223372036854775808,9223372036854775807)
primIntBounds (DatatypeUint8 _) = (0,255)
primIntBounds (DatatypeUint16 _) = (0,65535)
primIntBounds (DatatypeUint32 _) = (0,4294967295)
primIntBounds (DatatypeUint64 _) = (0,18446744073709551615)
primIntBounds (DatatypeUint _) = (0,18446744073709551615)
primIntBounds (DatatypeXorUint8 _) = (0,255)
primIntBounds (DatatypeXorUint16 _) = (0,65535)
primIntBounds (DatatypeXorUint32 _) = (0,4294967295)
primIntBounds (DatatypeXorUint64 _) = (0,18446744073709551615)
primIntBounds (DatatypeXorUint _) = (0,18446744073709551615)
primIntBounds _ = (0,-1) -- nonsensical bounds

primFloatBounds :: PrimitiveDatatype () -> (Double,Double)
primFloatBounds (DatatypeFloat _) = (-2.802597 * 10 ^(-45),3.402823 * (10 ^38))
primFloatBounds (DatatypeFloat32 _) = (-2.802597 * 10 ^(-45),3.402823 * (10 ^38))
primFloatBounds (DatatypeFloat64 _) = (-4.940656 * 10 ^ (-324),1.797693 * (10 ^308))
primFloatBounds _ = (0,-1) -- nonsensical bounds

indexType :: Type
indexType = PrimType $ DatatypeUint64 ()

bytesType :: Type
bytesType = CType Public (PrimType $ DatatypeUint8 ()) (integerExpr 1) []

stringType :: Type
stringType = PrimType $ DatatypeString ()

boolType :: Type
boolType = PrimType $ DatatypeBool ()

isPublicType :: Type -> Bool
isPublicType Public = True
isPublicType _ = False
