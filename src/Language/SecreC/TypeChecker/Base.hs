{-# LANGUAGE FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars

import Data.Maybe
import Data.Monoid
import Data.Generics
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Control.Monad.State as State
import Control.Monad.Reader
import Control.Monad.Except

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
    , templateConstraints :: [TCstr] -- a set of inferred template constraints
    }
  deriving Functor

vars env = Map.union (localVars env) (globalVars env)

-- | Adds a new template constraint to the environment
addTemplateConstraint :: TCstr -> TcM loc ()
addTemplateConstraint cstr = modify (\env -> env { templateConstraints = cstr : templateConstraints env })

insideTemplate :: TcM loc Bool
insideTemplate = liftM inTemplate State.get

resetLocal :: TcEnv loc -> TcEnv loc
resetLocal e = e { localVars = Map.empty }

emptyTcEnv :: TcEnv loc
emptyTcEnv = TcEnv Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty False []

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
            dvars <- getVars GlobalScope DomainC
            case Map.lookup n dvars of
                Just e -> return $ entryType e
                Nothing -> tcError (locpos l) $ NotDefinedDomain n

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkNonTemplateType :: Location loc => TypeName loc -> TcReaderM loc Type
checkNonTemplateType tn@(TypeName l n) = do
    es <- checkType tn
    case es of
        [e] -> return $ entryType e 
        es -> tcError (locpos l) $ NoNonTemplateType n
    
-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: Location loc => TypeName loc -> TcReaderM loc [EntryEnv loc]
checkType (TypeName l n) = do
    ss <- liftM structs ask
    case Map.lookup n ss of
        Just (base,es) -> return (base : Map.elems es)
        Nothing -> do
            vars <- getVars GlobalScope TypeStarC
            case Map.lookup n vars of
                Just e -> return [ e { entryType = TVar (Typed n $ entryType e) } ]
                Nothing -> tcError (locpos l) $ NotDefinedType n

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
addTemplateOperator :: Location loc => [Typed Identifier] -> Op (Typed loc) -> TcM loc ()
addTemplateOperator vars op = do
    let Typed l t = loc op
    let o = fmap (const ()) op
    cstrs <- liftM templateConstraints get
    let e = EntryEnv l (TpltType vars cstrs [] t)
    modify $ \env -> env { operators = Map.update (Just . Map.insert (locpos l) e) o (operators env) }

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: Location loc => Op (Typed loc) -> TcM loc ()
newOperator op = do
    let Typed l t = loc op
    let o = fmap (const ()) op
    let e = EntryEnv l t
    modify $ \env -> env { operators = Map.update (Just . Map.insert (locpos l) e) o (operators env) }
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: Location loc => [Typed Identifier] -> ProcedureName (Typed loc) -> TcM loc ()
addTemplateProcedure vars (ProcedureName (Typed l t) n) = do
    cstrs <- liftM templateConstraints get
    let e = EntryEnv l (TpltType vars cstrs [] t)
    modify $ \env -> env { procedures = Map.update (Just . Map.insert (locpos l) e) n (procedures env) }

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: Location loc => ProcedureName (Typed loc) -> TcM loc ()
newProcedure (ProcedureName (Typed l t) n) = do
    let e = EntryEnv l t
    modify $ \env -> env { procedures = Map.update (Just . Map.insert (locpos l) e) n (procedures env) }
  
 -- | Checks that a procedure exists.
checkProcedure :: Location loc => ProcedureName loc -> TcReaderM loc [EntryEnv loc]
checkProcedure (ProcedureName l n) = do
    ps <- liftM procedures ask
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ NotDefinedProcedure n
        Just es -> return $ Map.elems es
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: Location loc => [Typed Identifier] -> TypeName (Typed loc) -> TcM loc ()
addTemplateStruct vars (TypeName (Typed l struct) n) = do
    cstrs <- liftM templateConstraints get
    let e = EntryEnv l $ TpltType vars cstrs [] struct
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate n (locpos $ loc base)
        Nothing -> modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: Location loc => [Typed Identifier] -> [Type] -> TypeName (Typed loc) -> TcM loc ()
addTemplateStructSpecialization vars specials (TypeName (Typed l struct) n) = do
    cstrs <- liftM templateConstraints get
    let e = EntryEnv l $ TpltType vars cstrs specials struct
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
    State.modify (\env -> env { inTemplate = True, templateConstraints = [] })
    x <- m
    State.modify (\env -> env { inTemplate = False, templateConstraints = [] })
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

-- | A template constraint
-- Left = type constraint
-- Right = procedure constraint
data TCstr = TCstr (Either Identifier Identifier) [Type]
  deriving (Read,Show,Data,Typeable,Eq,Ord)

instance Vars TCstr where
    type VarOf TCstr = Typed Identifier
    fvs (TCstr _ ts) = fvsFoldable ts
    bvs (TCstr _ ts) = bvsFoldable ts

instance Subst TCstr where
    type SubstOf TCstr = Type
    subst s (TCstr n ts) = TCstr n (substTraversable s ts)

-- | Template application dictionary
newtype TDict = TDict { unTDict :: (Map (Identifier,[Type]) Position) }
  deriving (Read,Show,Data,Typeable,Eq,Ord)

lookupTDict :: Identifier -> [Type] -> TDict -> Maybe Position
lookupTDict i args = Map.lookup (i,args) . unTDict

instance Monoid TDict where
    mempty = TDict Map.empty
    mappend (TDict xs) (TDict ys) = TDict $ Map.union xs ys

instance Vars TDict where
    type VarOf TDict = Typed Identifier
    fvs (TDict m) = Set.foldl' (\s (_,ts) -> s `Set.union` fvsFoldable ts) Set.empty $ Map.keysSet m
    bvs (TDict m) = Set.foldl' (\s (_,ts) -> s `Set.union` bvsFoldable ts) Set.empty $ Map.keysSet m

instance Subst TDict where
    type SubstOf TDict = Type
    subst s (TDict m) = TDict $ Map.mapKeys (\(n,ts) -> (n,substTraversable s ts)) m

data Type
    = NoType -- ^ For locations with no associated type information
    | ProcType -- ^procedure type
        [VarName Type] -- typed procedure arguments
        Type -- return type
    | StructType -- ^ Struct type
            [Attribute Type] -- ^ typed arguments
    | TApp -- template application
            Identifier -- ^ template name
            [Type] -- ^ template argument types
            TDict -- ^ reference to a dictionary to be used for inner template applications
    | TpltType -- ^ Template type
            [Typed Identifier] -- ^ template variables
            [TCstr] -- ^ template constraints depending on the variables
            [Type] -- ^ template specializations
            Type -- ^ template's type
    | TVar -- ^ type variable
        (Typed Identifier) -- ^ variable name
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
  deriving (Read,Show,Data,Typeable,Eq,Ord)

data TypeClass
    = KindStarC -- type of kinds
    | KindC -- kinds
    | DomainC -- for typed domains
    | TypeStarC -- type of types
    | TypeC -- regular type
    | DimC -- dimension type
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
                             | t == largestInt = DimC -- dimension variables
typeClass _ = TypeC

typedScVar :: ScVar Type -> Typed Identifier
typedScVar (ScVar t i) = Typed i t

instance Vars Type where
    type VarOf Type = Typed Identifier
    fvs NoType = Set.empty
    fvs (ProcType vs t) = fvsFoldable (map (\(VarName l _) -> l) vs) `Set.union` fvs t
    fvs (StructType as) = Set.map typedScVar $ fvsFoldable as
    fvs (TApp n ts dict) = fvsFoldable ts `Set.union` fvs dict
    fvs (TpltType vs cs ss t) = (fvsFoldable cs `Set.union` fvsFoldable ss `Set.union` fvs t) `Set.difference` (Set.fromList vs)
    fvs (TVar v) = Set.singleton v
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
    bvs NoType = Set.empty
    bvs (ProcType vs t) = bvsFoldable (map (\(VarName l _) -> l) vs) `Set.union` bvs t
    bvs (StructType as) = Set.map typedScVar $ bvsFoldable as
    bvs (TApp n ts dict) = fvsFoldable ts `Set.union` fvs dict
    bvs (TpltType vs cs ss t) = Set.fromList vs `Set.union` bvsFoldable cs `Set.union` bvsFoldable ss `Set.union` bvs t
    bvs (TVar v) = Set.empty
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

instance Subst Type where
    type SubstOf Type = Type
    subst f NoType = NoType
    subst f (ProcType vs t) = ProcType (map (fmap (subst f)) vs) (subst f t)
    subst f (StructType as) = StructType $ map (fmap (subst f)) as
    subst f (TApp n ts dict) = TApp n (map (subst f) ts) (subst f dict)
    subst f (TpltType vs cs ss t) = TpltType (map (mapTyped (subst g)) vs) (map (subst g) cs) (map (subst g) ss) (subst g t)
        -- we don't substitute the template's variables, that may shadow the substitution variables
        where g v = if List.elem (unTyped v) (map unTyped vs) then Nothing else f v
    subst f (TVar v) = case f v of
        Nothing -> TVar v
        Just t -> t
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
        
-- | Update the size of a compound type
refineTypeSizes :: Type -> Maybe (Sizes loc) -> Type
refineTypeSizes (CType s t d sz) Nothing = CType s t d []
refineTypeSizes (CType s t d sz) (Just ss) = let Sizes sz' = fmap (const ()) ss in CType s t d $ Foldable.toList sz'
refineTypeSizes _ _ = error "no size"

--integerLitExpr :: Location loc => Expression loc -> TcReaderM loc (Maybe (Expression loc,Int))

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
  deriving (Read,Show,Data,Typeable,Functor,Eq,Ord)

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

largestInt :: Type
largestInt = PrimType $ DatatypeUint64 ()

prove :: TcReaderM loc a -> TcReaderM loc (Maybe a)
prove proof = catchError (liftM Just proof) (const $ return Nothing)

-- checks if two types are equal, without using coercions, while performing substitutions on both sides
-- must define new type variables for applied substitutions
equals :: Location loc => loc -> Type -> Type -> TcReaderM loc (Substs Type)
equals = undefined -- TODO

equalsList :: Location loc => loc -> [Type] -> [Type] -> TcReaderM loc (Substs Type)
equalsList l [] [] = return $ emptySubsts (Proxy::Proxy Type)
equalsList l (x:xs) (y:ys) = do
    f <- equals l x y
    g <- equalsList l xs ys
    return (appendSubsts (Proxy::Proxy Type) f g)
equalsList l xs ys = tcError (locpos l) $ EqualityException "Different number of arguments"

-- checks if two types are equal by applying implicit coercions, while performing substitutions on both sides
-- directed coercion
coerces :: loc -> Type -> Type -> TcReaderM loc (Substs Type)
coerces = undefined -- TODO

-- | Checks if a type is more specific than another
compares :: loc -> Type -> Type -> TcReaderM loc Ordering
compares l t1 t2 = undefined -- TODO
    
comparesList :: Location loc => loc -> [Type] -> [Type] -> TcReaderM loc Ordering
comparesList l [] [] = return EQ
comparesList l (x:xs) (y:ys) = do
    f <- compares l x y
    g <- comparesList l xs ys
    appendOrdering f g
  where
    appendOrdering EQ y = return y
    appendOrdering x EQ = return x
    appendOrdering x y = if x == y then return x else tcError (locpos l) $ ComparisonException "Non-comparable types"
comparesList l xs ys = tcError (locpos l) $ ComparisonException "Different number of arguments"
    
-- | Non-directed unification, with coercions
-- takes a type variable for the result of the unification
unifies :: Location loc => loc -> Typed Identifier -> Type -> Type -> TcReaderM loc (Substs Type)
unifies = undefined -- TODO

--coercesInto :: Location loc => loc -> Typed Identifier -> Type -> Type -> TcReaderM loc (Substs Type)
--coercesInto l x t1 t2 = do
--    s1 <- coerces l t1 (TVar x)
--    s2 <- coerces l t2 (TVar x)
--    return $ appendSubsts s1 s2
    
-- propagates a dictionary down to template applications
addTDict :: TDict -> Type -> Type
addTDict dict = everywhere (mkT (`mappend` dict))

-- | Creates a distinct head signature from a template type declaration
-- Rename variables to make sure that they are unique to this signature
uniqueTemplateArgs :: Location loc => Identifier -> EntryEnv loc -> [Type]
uniqueTemplateArgs name e = case entryType e of
--    TpltType args cstrs [] (ProcType )
    TpltType args cstrs [] body -> map (uniqueVars . TVar) args -- a base template uses the base arguments
    TpltType args cstrs specials body -> map uniqueVars specials -- a specialization uses the specialized arguments
  where uniqueVars (TVar (Typed v t)) = TVar (Typed (ppr (locpos (entryLoc e)) ++ "." ++ v) t)

boolType :: Type
boolType = PrimType $ DatatypeBool ()

-- declassifies 
declassifyType :: Location loc => loc -> Type -> TcReaderM loc Type
declassifyType l (CType _ t d sz) = return $ CType Public t d sz
declassifyType l t | typeClass t == TypeC = return t
                 | otherwise = tcError (locpos l) $ NonDeclassifiableExpression

-- | Operation supported over the given type
isSupportedOp :: Op () -> Type -> TcReaderM loc ()
isSupportedOp (OpMul ()) = undefined -- TODO
isSupportedOp (OpDiv ()) = undefined -- TODO
isSupportedOp (OpMod ()) = undefined -- TODO
isSupportedOp (OpAdd ()) = undefined -- TODO
isSupportedOp (OpSub ()) = undefined -- TODO
isSupportedOp (OpBand ()) = undefined -- TODO
isSupportedOp (OpBor ()) = undefined -- TODO
isSupportedOp (OpXor ()) = undefined -- TODO


