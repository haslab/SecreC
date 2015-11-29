{-# LANGUAGE ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars

import Data.Int
import Data.Word
import Data.Maybe
import Data.Monoid hiding ((<>))
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

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as Pretty

-- warn for unused local variables

data Scope = GlobalScope | LocalScope
  deriving (Show,Read,Data,Typeable)

data TcEnv loc = TcEnv {
      globalVars :: Map VarIdentifier (EntryEnv loc) -- ^ global variables: name |-> type of the variable
    , localVars  :: Map VarIdentifier (EntryEnv loc) -- ^ local variables: name |-> type of the variable
    , kinds :: Map VarIdentifier (EntryEnv loc) -- ^ defined kinds: name |-> type of the kind
    , domains :: Map VarIdentifier (EntryEnv loc) -- ^ defined domains: name |-> type of the domain
    -- a list of overloaded operators; akin to Haskell type class operations
    -- we don't allow specialization of function templates
    , operators :: Map (Op ()) (Map TyVarId (EntryEnv loc)) -- ^ defined operators: name |-> procedure decl
    -- a list of overloaded procedures; akin to Haskell type class operations
    -- we don't allow specialization of function templates
    , procedures :: Map VarIdentifier (Map TyVarId (EntryEnv loc)) -- ^ defined procedures: name |-> procedure decl
    -- | a base template and a list of specializations; akin to Haskell type functions
    , structs :: Map VarIdentifier (EntryEnv loc,Map TyVarId (EntryEnv loc)) -- ^ defined structs: name |-> struct decl
    , inTemplate :: Bool -- ^ @True@ if we are type checking the body of a template declaration
    , tDict :: TDict loc -- a dictionary with a set of inferred constraints and resolved constraints
    , tyVarId :: TyVarId
    }
  deriving Functor

addValueM :: Location loc => loc -> VarName VarIdentifier (Typed loc) -> Expression VarIdentifier (Typed loc) -> TcM loc ()
addValueM l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
addValueM l (VarName t n) e | typeClass (typed t) == typeClass (typed $ loc e) =
    modify $ \env -> env { tDict = (tDict env) { tValues = Map.insert (VarName () n) e (tValues $ tDict env) } } 
addValueM l v e = genericError (locpos l) $ "unification: mismatching expression types"

vars env = Map.union (localVars env) (globalVars env)

insideTemplate :: TcM loc Bool
insideTemplate = liftM inTemplate State.get

emptyTcEnv :: TcEnv loc
emptyTcEnv = TcEnv Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty False mempty 0

data EntryEnv loc = EntryEnv {
      entryLoc :: loc -- ^ Location where the entry is defined
    , entryType :: Type -- ^ Type of the entry
    , entryValue :: EntryValue loc
    }
  deriving Functor
  
data EntryValue loc
    = UnknownValue
    | NoValue
    | KnownExpression (Expression VarIdentifier (Typed loc))
 deriving (Show,Functor,Typeable,Eq,Ord)

instance (Location loc,Vars loc) => Vars (EntryValue loc) where
    traverseVars f (KnownExpression e) = do
        e' <- f e
        return $ KnownExpression e
    traverseVars f v = return v

instance Location loc => Located (EntryEnv loc) where
    type LocOf (EntryEnv loc) = loc
    loc = entryLoc
    updLoc e l = e { entryLoc = l }

instance PP (EntryValue loc) where
    pp UnknownValue = text "unknown"
    pp NoValue = text "novalue"
    pp (KnownExpression e) = pp e

-- | Gets the variables of a given type class
getVars :: Location loc => Scope -> TypeClass -> TcM loc (Map VarIdentifier (EntryEnv loc))
getVars GlobalScope c = do
    vs <- liftM globalVars State.get
    return $ Map.filter (\e -> typeClass (entryType e) == c) vs
getVars LocalScope c = do
    vs <- liftM vars State.get
    return $ Map.filter (\e -> typeClass (entryType e) == c) vs

addVar :: Location loc => Scope -> VarIdentifier -> EntryEnv loc -> TcM loc ()
addVar GlobalScope n e = modify $ \env -> env { globalVars = Map.insert n e (globalVars env) }
addVar LocalScope n e = modify $ \env -> env { localVars = Map.insert n e (localVars env) }

checkVariable :: Location loc => Scope -> VarName VarIdentifier loc -> TcM loc Type
checkVariable scope (VarName l n) = do
    vs <- getVars scope TypeC
    case Map.lookup n vs of
        Just e -> return $ entryType e
        Nothing -> tcError (locpos l) $ VariableNotFound (ppVarId n)

-- | Adds a new variable to the environment
newVariable :: Location loc => Scope -> VarName VarIdentifier (Typed loc) -> EntryValue loc -> TcM loc ()
newVariable scope (VarName (Typed l t) n) val = do
    vars <- getVars scope TypeC
    case Map.lookup n vars of
        Just e -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
        Nothing -> return ()
    addVar scope n (EntryEnv l t val)

-- | Adds a new domain variable to the environment
newDomainVariable :: Location loc => Scope -> DomainName VarIdentifier (Typed loc) -> TcM loc ()
newDomainVariable scope (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ InvalidDomainVariableName (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            vars <- getVars scope KindC
            case Map.lookup n vars of
                Just e -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
                Nothing -> addVar scope n (EntryEnv l t UnknownValue)

-- | Adds a new type variable to the environment
newTypeVariable :: Location loc => Scope -> TypeName VarIdentifier (Typed loc) -> TcM loc ()
newTypeVariable scope (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (b,es) -> tcError (locpos l) $ InvalidTypeVariableName (ppVarId n) (map (locpos . entryLoc) (b:Map.elems es))
        Nothing -> do
            vars <- getVars scope TypeStarC
            case Map.lookup n vars of
                Just e -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
                Nothing -> addVar scope n (EntryEnv l t UnknownValue)

-- | Adds a new domain to the environment
newDomain :: Location loc => DomainName VarIdentifier (Typed loc) -> TcM loc ()
newDomain (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ MultipleDefinedDomain (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t UnknownValue
            modify $ \env -> env { domains = Map.insert n e (domains env) }

-- | Checks if a domain exists in scope, and returns its type
-- Searches for both user-defined private domains and domain variables
checkDomain :: Location loc => DomainName VarIdentifier loc -> TcM loc Type
checkDomain (DomainName l n) = do
    ds <- liftM domains State.get
    case Map.lookup n ds of
        Just e -> case entryType e of
            DType (Just k) -> return $ Private (DomainName () n) k
        Nothing -> do
            dvars <- getVars LocalScope KindC
            case Map.lookup n dvars of
                Just e -> return $ TVar $ VarName (entryType e) n
                Nothing -> tcError (locpos l) $ NotDefinedDomain (ppVarId n)
    
-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: Location loc => TypeName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkType (TypeName l n) = do
    ss <- liftM structs State.get
    case Map.lookup n ss of
        Just (base,es) -> return (base : Map.elems es)
        Nothing -> do
            vars <- getVars LocalScope TypeStarC
            case Map.lookup n vars of
                Just e -> return [ e { entryType = TVar (VarName (entryType e) n) } ] -- return the type variable
                Nothing -> tcError (locpos l) $ NotDefinedType (ppVarId n)

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkNonTemplateType :: Location loc => TypeName VarIdentifier loc -> TcM loc Type
checkNonTemplateType tn@(TypeName l n) = do
    es <- checkType tn
    case es of
        [e] -> return $ entryType e 
        es -> tcError (locpos l) $ NoNonTemplateType (ppVarId n)

-- | Checks if a template type exists in scope
-- Returns all template type declarations in scope, base template first
checkTemplateType :: Location loc => TypeName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkTemplateType ty@(TypeName _ n) = do
    es <- checkType ty
    let check e = case entryType e of
                    TType {} -> return ()
                    otherwise -> tcError (locpos $ loc ty) $ NoTemplateType (ppVarId n) (locpos $ entryLoc e)
    mapM_ check es
    return es

-- | Checks if a variable argument of a template exists in scope
-- The argument can be a (user-defined or variable) type, a (user-defined or variable) domain or a dimension variable
checkTemplateArg :: Location loc => TemplateArgName VarIdentifier loc -> TcM loc Type
checkTemplateArg (TemplateArgName l vn) = do
    env <- State.get
    let ss = structs env
    let ds = domains env
    let vs = vars env
    case (Map.lookup vn ss,Map.lookup vn ds,Map.lookup vn vs) of
        (Just (base,es),Nothing,Nothing) -> case (base:Map.elems es) of
            [e] -> case entryType e of
                TpltType {} -> tcError (locpos l) $ NoNonTemplateType (ppVarId vn)
                t -> return t
            es -> tcError (locpos l) $ NoNonTemplateType (ppVarId vn)
        (Nothing,Just e,Nothing) -> return $ entryType e
        (Nothing,Nothing,Just e) -> return $ entryType e
        (mb1,mb2,mb3) -> tcError (locpos l) $ AmbiguousName (ppVarId vn) $ map (locpos . entryLoc) $ maybe [] (\(b,es) -> b:Map.elems es) mb1 ++ maybeToList mb2 ++ maybeToList mb3

-- | Checks that a kind exists in scope
checkKind :: Location loc => KindName VarIdentifier loc -> TcM loc ()
checkKind (KindName l n) = do
    ks <- liftM kinds State.get
    case Map.lookup n ks of
        Just e -> return ()
        Nothing -> tcError (locpos l) $ NotDefinedKind (ppVarId n)

-- | Adds a new kind to the environment
newKind :: Location loc => KindName VarIdentifier (Typed loc) -> TcM loc ()
newKind (KindName (Typed l t) n) = do
    ks <- liftM kinds get
    case Map.lookup n ks of
        Just e -> tcError (locpos l) $ MultipleDefinedKind (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t UnknownValue
            modify $ \env -> env { kinds = Map.insert n e (kinds env) } 

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: Location loc => [VarName VarIdentifier Type] -> Op (Typed loc) -> TcM loc ()
addTemplateOperator vars op = do
    let Typed l t = loc op
    let o = fmap (const ()) op
    cstrs <- liftM (tDict) get
    i <- newTyVarId
    let e = EntryEnv l (TpltType i vars (fmap locpos cstrs) [] t) UnknownValue
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: Location loc => Op (Typed loc) -> TcM loc ()
newOperator op = do
    let Typed l t = loc op
    let o = fmap (const ()) op
    let e = EntryEnv l t UnknownValue
    modify $ \env -> env { operators = Map.alter (Just . Map.insert (typeTyVarId t) e . maybe Map.empty id) o (operators env) }
  
 -- | Checks that an oeprator exists.
checkOperator :: Location loc => Op loc -> TcM loc [EntryEnv loc]
checkOperator op = do
    ps <- liftM operators State.get
    let cop = fmap (const ()) op
    case Map.lookup cop ps of
        Nothing -> tcError (locpos $ loc op) $ NotDefinedOperator cop
        Just es -> return $ Map.elems es
  
inheritedTDict :: Location loc => loc -> TDict loc -> TDict loc
inheritedTDict l d = d { tCstrs = Map.mapKeys (\(Loc l1 c) -> Loc l $ InheritedCstr (locpos l1) c) (tCstrs d) }
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: Location loc => [VarName VarIdentifier Type] -> ProcedureName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateProcedure vars (ProcedureName (Typed l t) n) = do
    cstrs <- liftM (tDict) get
    i <- newTyVarId
    let e = EntryEnv l (TpltType i vars (fmap locpos cstrs) [] t) UnknownValue
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: Location loc => ProcedureName VarIdentifier (Typed loc) -> TcM loc ()
newProcedure (ProcedureName (Typed l t) n) = do
    let e = EntryEnv l t UnknownValue
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert (typeTyVarId t) e . maybe Map.empty id) n (procedures env) }
  
 -- | Checks that a procedure exists.
checkProcedure :: Location loc => ProcedureName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkProcedure (ProcedureName l n) = do
    ps <- liftM procedures State.get
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ NotDefinedProcedure (ppVarId n)
        Just es -> return $ Map.elems es
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: Location loc => [VarName VarIdentifier Type] -> TypeName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateStruct vars (TypeName (Typed l struct) n) = do
    cstrs <- liftM (tDict) get
    i <- newTyVarId
    let e = EntryEnv l (TpltType i vars (fmap locpos cstrs) [] struct) UnknownValue
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate (ppVarId n) (locpos $ loc base)
        Nothing -> modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: Location loc => [VarName VarIdentifier Type] -> [Type] -> TypeName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateStructSpecialization vars specials (TypeName (Typed l struct) n) = do
    cstrs <- liftM (tDict) get
    i <- newTyVarId
    let e = EntryEnv l (TpltType i vars (fmap locpos cstrs) specials struct) UnknownValue
    let mergeStructs (b1,s1) (b2,s2) = (b2,s1 `Map.union` s2)
    modify $ \env -> env { structs = Map.update (\(b,s) -> Just (b,Map.insert i e s)) n (structs env) }

-- | Defines a new struct type
newStruct :: Location loc => TypeName VarIdentifier (Typed loc) -> TcM loc ()
newStruct (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStruct (ppVarId n) (locpos $ entryLoc base)
        Nothing -> do
            let e = EntryEnv l t UnknownValue
            modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }

type TcM loc = StateT (TcEnv loc) SecrecM

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
    State.modify (\env -> env { inTemplate = True, tDict = mempty })
    x <- m
    State.modify (\env -> env { inTemplate = False, tDict = mempty })
    return x

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: TcM loc a -> TcM loc a
tcBlock m = do
    s <- get
    (x,s') <- lift $ runStateT m s
    modify $ \env -> env { tyVarId = tyVarId s' }
    return x

tcBlockWith :: TcM loc a -> TcM loc (a,TDict loc)
tcBlockWith m = do
    s <- get
    (x,env') <- lift $ runStateT m s
    State.modify $ \env -> env' { tDict = tDict env }
    return (x,tDict env')

runTcM :: Location loc => TcM loc a -> SecrecM a
runTcM m = evalStateT m emptyTcEnv

type PIdentifier = Either (ProcedureName VarIdentifier ()) (Op ())

-- | A template constraint with a result type
data TCstr
    = TApp (TypeName VarIdentifier ()) [Type] -- ^ type template application
    | TDec (TypeName VarIdentifier ()) [Type] -- ^ type template declaration
    | PDec PIdentifier [Type] Type -- ^ procedure declaration, incl. return type
    | Coerces Type Type -- ^ types coercible
    | Unifies Type Type -- ^ unification
    | SupportedPrint [Type] -- ^ can call tostring on the argument type
    | ProjectStruct Type (AttributeName VarIdentifier ()) -- ^ struct type projection
    | ProjectMatrix Type [ArrayProj] -- ^ matrix type projection
    | IsReturnStmt (Set StmtClass) Type (ProcedureDeclaration VarIdentifier Position) -- ^ is return statement
    | Cast -- ^ type cast
        Type -- ^ from
        Type -- ^ to
    | InheritedCstr Position TCstr
    | GetCBase -- ^ get the base of a complex type
        Type
    | SetCBase -- ^ set the base of a complex type
        Type -- ^ compelx type
        Type -- ^ new base
  deriving (Data,Typeable,Show,Eq,Ord)
    
instance PP TCstr where
    pp (TApp n ts) = text "tapp" <+> pp n <+> sepBy space (map pp ts)
    pp (TDec n ts) = text "tdec" <+> pp n <+> sepBy space (map pp ts)
    pp (PDec n ts r) = text "pdec" <+> pp n <+> parens (sepBy comma (map pp ts)) <+> pp r
    pp (Coerces t1 t2) = text "coerces" <+> pp t1 <+> pp t2
    pp (Unifies t1 t2) = text "unifies" <+> pp t1 <+> pp t2
    pp (SupportedPrint ts) = text "print" <+> sepBy space (map pp ts)
    pp (ProjectStruct t a) = pp t <> char '.' <> pp a
    pp (ProjectMatrix t as) = pp t <> brackets (sepBy comma $ map pp as) 
    pp (IsReturnStmt cs t dec) = text "return" <+> (hcat $ map pp $ Set.toList cs) <+> pp t <+> pp dec
    pp (Cast from to) = text "cast" <+> pp from <+> pp to
    pp (InheritedCstr p c) = text "inherited from" <+> pp p <+> pp c
    pp (GetCBase t) = text "getcbase" <+> pp t
    pp (SetCBase t p) = text "setcbase" <+> pp t <+> pp p
    
data ArrayProj
    = ArraySlice ArrayIndex ArrayIndex
    | ArrayIdx ArrayIndex
  deriving (Data,Typeable,Show)
    
instance Eq ArrayProj where
    (ArraySlice i1 i2) == (ArraySlice i3 i4) = i1 == i3 && i2 == i4
    (ArrayIdx w1) == (ArrayIdx w2) = w1 == w2
    x == y = False
instance Ord ArrayProj where
    compare (ArraySlice i1 i2) (ArraySlice i3 i4) = compare i1 i3 `mappend` compare i2 i4
    compare (ArrayIdx w1) (ArrayIdx w2) = compare w1 w2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)
    
instance PP ArrayProj where
    pp (ArraySlice i1 i2) = pp i1 <> char ':' <> pp i2
    pp (ArrayIdx w) = pp w
    
instance Vars ArrayProj where
    traverseVars f (ArraySlice i1 i2) = do
        i1' <- f i1
        i2' <- f i2
        return $ ArraySlice i1' i2'
    traverseVars f (ArrayIdx w) = do
        w' <- f w
        return $ ArrayIdx w'
    
data ArrayIndex
    = NoArrayIndex
    | StaticArrayIndex Word64
    | DynArrayIndex (Expression VarIdentifier Type) SecrecError
  deriving (Data,Typeable,Show)

instance Eq ArrayIndex where
    NoArrayIndex == NoArrayIndex = True
    (StaticArrayIndex w1) == (StaticArrayIndex w2) = w1 == w2
    (DynArrayIndex e1 _) == (DynArrayIndex e2 _) = e1 == e2
    x == y = False
instance Ord ArrayIndex where
    compare NoArrayIndex NoArrayIndex = EQ
    compare (StaticArrayIndex w1) (StaticArrayIndex w2) = compare w1 w2
    compare (DynArrayIndex e1 _) (DynArrayIndex e2 _) = compare e1 e2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)
  
instance PP ArrayIndex where
    pp NoArrayIndex = PP.empty
    pp (StaticArrayIndex w) = pp w
    pp (DynArrayIndex e err) = pp e
    
instance Vars ArrayIndex where
    traverseVars f NoArrayIndex = return NoArrayIndex
    traverseVars f (StaticArrayIndex w) = do
        w' <- f w
        return $ StaticArrayIndex w'
    traverseVars f (DynArrayIndex e err) = do
        e' <- f e
        return $ DynArrayIndex e' err
    
arrayIndexExpr :: ArrayIndex -> Expression VarIdentifier Type
arrayIndexExpr (StaticArrayIndex w) = indexExpr w
arrayIndexExpr (DynArrayIndex e _) = e
    
arrayIndexErr :: ArrayIndex -> Maybe SecrecError
arrayIndexErr (DynArrayIndex _ err) = Just err
arrayIndexErr _ = Nothing
    
instance Vars TCstr where
    traverseVars f (TApp n args) = do
        n' <- f n
        args' <- mapM f args
        return $ TApp n' args'
    traverseVars f (TDec n args) = do
        n' <- f n
        args' <- mapM f args
        return $ TDec n' args'
    traverseVars f (PDec n args ret) = do
        n' <- f n
        args' <- mapM f args
        ret' <- f ret
        return $ PDec n' args' ret'
    traverseVars f (Coerces t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Coerces t1' t2'
    traverseVars f (Unifies t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Unifies t1' t2'
    traverseVars f (SupportedPrint ts) = do
        ts' <- mapM f ts
        return $ SupportedPrint ts'
    traverseVars f (ProjectStruct t a) = do
        t' <- f t
        a' <- f a
        return $ ProjectStruct t' a'
    traverseVars f (ProjectMatrix t is) = do
        t' <- f t
        is' <- mapM f is
        return $ ProjectMatrix t' is'
    traverseVars f (IsReturnStmt cs t p) = do
        cs' <- mapSetM f cs
        t' <- f t
        p' <- f p
        return $ IsReturnStmt cs' t' p'
    traverseVars f (Cast from to) = do
        from' <- f from
        to' <- f to
        return $ Cast from' to'
    traverseVars f (InheritedCstr p k) = do
        p' <- f p
        k' <- f k
        return $ InheritedCstr p' k'
    traverseVars f (GetCBase t) = do
        t' <- f t
        return $ GetCBase t'
    traverseVars f (SetCBase t p) = do
        t' <- f t
        p' <- f p
        return $ SetCBase t' p'

-- | Template constraint dictionary: Mappings from keys @TCstr t@ to values @t@, and type variable substitutions
type SubstsType = Map (VarName VarIdentifier ()) Type
type SubstsVal loc = Map (VarName VarIdentifier ()) (Expression VarIdentifier (Typed loc))

type SubstsGeneric loc = Map (VarName VarIdentifier ()) (Either Type (Expression VarIdentifier (Typed loc)))

data TDict loc = TDict
    { tCstrs :: Map (Loc loc TCstr) (Maybe Type)
    , tSubsts :: SubstsType -- type substitions
    , tValues :: SubstsVal loc -- index value substitutions
    }
  deriving (Typeable,Eq,Ord,Show,Data)

tSolved :: TDict loc -> Map (Loc loc TCstr) Type
tSolved = Map.foldrWithKey (\k v m -> maybe m (\x -> Map.insert k x m) v) Map.empty . tCstrs

extractUnsolved :: TcM loc [Loc loc TCstr]
extractUnsolved = liftM (tUnsolved . tDict) State.get

addUnsolved :: [Loc loc TCstr] -> TcM loc ()
addUnsolved us = State.modify $ \env -> env { tDict = (tDict env) { tCstrs = tCstrs (tDict env) `Map.union` Map.fromList (zip us (repeat Nothing)) } }

tUnsolved :: TDict loc -> [Loc loc TCstr]
tUnsolved = Map.keys . Map.filter isNothing . tCstrs

instance Functor TDict where
    fmap f dict = dict { tCstrs = Map.mapKeys (mapLoc f) (tCstrs dict)
                       , tValues = Map.map (fmap (fmap f)) (tValues dict) }

insertTDictCstr :: loc -> TCstr -> Maybe Type -> TDict loc -> TDict loc
insertTDictCstr l c res dict = dict { tCstrs = Map.insert (Loc l c) res (tCstrs dict) }

addDict :: Location loc => TDict loc -> TcM loc ()
addDict d = modify $ \env -> env { tDict = mappend (tDict env) d }

---- | Adds a new template constraint to the environment
addTemplateConstraint :: loc -> TCstr -> Maybe Type -> TcM loc ()
addTemplateConstraint l c res = modify $ \env -> env { tDict = insertTDictCstr l c res (tDict env) }

addSubstM :: Location loc => loc -> VarName VarIdentifier Type -> Type -> TcM loc ()
addSubstM l v t | TVar v == t = return ()
              | typeClass (TVar v) == typeClass t = modify $ \env -> env { tDict = (tDict env) { tSubsts = Map.insert (fmap (const ()) v) t (tSubsts $ tDict env) } }
              | otherwise = genericError (locpos l) $ "unification: mismatching variable types"

instance Monoid (TDict loc) where
    mempty = TDict Map.empty Map.empty Map.empty
    mappend (TDict u1 ss1 ess1) (TDict u2 ss2 ess2) = TDict (u1 `Map.union` u2) (ss1 `Map.union` ss2) (ess1 `Map.union` ess2)

instance (Location loc,Vars loc) => Vars (TDict loc) where
    traverseVars f dict = varsBlock $ do
        vss' <- f $ tValues dict
        tss' <- f $ tSubsts dict
        let cstrs = tCstrs dict
        cstrs' <- Map.foldrWithKey (\k v m -> do { k' <- f k; v' <- f v; liftM (Map.insert k' v') m }) (return Map.empty) cstrs
        return $ TDict cstrs' tss' vss'

instance (Vars loc,Vars a) => Vars (Loc loc a) where
    traverseVars f (Loc l a) = do
        l' <- f l
        a' <- f a
        return $ Loc l' a'

substFromTDict :: (Vars loc,Location loc,Vars a) => TDict loc -> a -> a
substFromTDict dict = substFromSubstsType (tSubsts dict) . substFromSubstsVal (tValues dict)

substFromSubstsType :: Vars a => SubstsType -> a -> a
substFromSubstsType xs = substFromMap xs

substFromSubstsVal :: (Vars loc,Location loc,Vars a) => SubstsVal loc -> a -> a
substFromSubstsVal xs = substFromMap xs . substFromMap ys
    where
    ys = Map.map (fmap typed) xs

instance PP (TDict loc) where
    pp dict = text "Unsolved constraints:" $+$ nest 4 (vcat $ map pp $ tUnsolved dict)
          $+$ text "Type substitutions:" $+$ nest 4 (ppSubstsType (tSubsts dict))
          $+$ text "Value substitutions:" $+$ nest 4 (ppSubstsVal (tValues dict))
          $+$ text "Solved constraints:" $+$ nest 4 (vcat $ map ppSolved $ Map.toList $ tSolved dict)
     where ppSolved (k,NoType) = pp k
           ppSolved (k,t) = pp k <+> char '=' <+> pp t

data VarIdentifier = VarIdentifier
        { varIdBase :: Identifier
        , varIdUniq :: Maybe TyVarId
        }
    deriving (Typeable,Data,Show,Ord,Eq)

mkVarId :: Identifier -> VarIdentifier
mkVarId s = VarIdentifier s Nothing
    
uniqVarId :: Identifier -> TcM loc VarIdentifier
uniqVarId n = do
    i <- newTyVarId
    return $ VarIdentifier n (Just i)

instance PP VarIdentifier where
    pp = ppVarId

type TyVarId = Int

newTyVarId :: TcM loc TyVarId
newTyVarId = do
    i <- liftM tyVarId get
    modify $ \env -> env { tyVarId = succ (tyVarId env) }
    return i

newDomainTyVar :: Maybe (KindName VarIdentifier ()) -> TcM loc Type
newDomainTyVar k = do
    n <- uniqVarId "d"
    return $ TVar $ VarName (DType k) n

newDimVar :: TcM loc (Expression VarIdentifier Type)
newDimVar = do
    n <- uniqVarId "dim"
    return $ RVariablePExpr index $ VarName index n

newTyVar :: TcM loc Type
newTyVar = do
    n <- uniqVarId "t"
    return $ TVar (VarName TType n)
    
newSizeVar :: TcM loc (Expression VarIdentifier Type)
newSizeVar = do
    n <- uniqVarId "sz"
    return $ RVariablePExpr index $ VarName index n

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
        Position
        [VarName VarIdentifier Type] -- typed procedure arguments
        Type -- return type
        [Statement VarIdentifier (Typed Position)] -- ^ the procedure's body
    | StructType -- ^ Struct type
            TyVarId -- ^ unique structure declaration id
            Position -- ^ location of the procedure declaration
            [Attribute VarIdentifier Type] -- ^ typed arguments
    | TK -- ^ the result of resolving a constraint
        TCstr -- ^ a constraint returning a type
    | TpltType -- ^ Template type
            TyVarId -- ^ unique template declaration id
            [VarName VarIdentifier Type] -- ^ template variables
            (TDict Position) -- ^ template constraints depending on the variables
            [Type] -- ^ template specializations
            Type -- ^ template's type
    | TVar -- ^ type variable
        (VarName VarIdentifier Type) -- ^ typed variable name
    | TyLit -- ^ the most concrete type for a literal
        (Literal ()) -- ^ the literal itself
    | TType -- ^ Type of types
    | KType -- ^ Type of kinds
    | DType -- ^ Type of domains
        (Maybe (KindName VarIdentifier ())) -- ^ optional kind of the domain
    | Void -- ^ Empty type
    | StmtType (Set StmtClass) -- ^ Type of a @Statement@
    | CType -- ^ Compound SecreC type
        Type -- ^ security type
        Type -- ^ data type
        (Expression VarIdentifier Type) -- ^ dimension (default = 0, i.e., scalars)
        [Expression VarIdentifier Type] -- ^ sizes for each dimension (dependent types?) -- NOTE: check bounds if size is statically known?
    | PrimType (PrimitiveDatatype ())
    | Public -- ^ public domain
    | Private -- ^ private domain
        (DomainName VarIdentifier ()) -- ^ domain
        (KindName VarIdentifier ()) -- ^ kind
    | SysPush Type
    | SysRet Type
    | SysRef Type
    | SysCRef Type
  deriving (Typeable)

instance PP Type where
    pp t@NoType = text (show t)
    pp t@(ProcType _ _ vars ret stmts) =
        ptext "procedure"
        <+> parens (sepBy comma $ map ppProcArg vars)
        <+> pp ret
        <+> pp stmts
      where ppProcArg (VarName t n) = pp t <+> pp n
    pp t@(StructType _ _ atts) = text "struct" <+> braces (sepBy (char ';') $ map ppStructAtt atts)
    pp t@(TK c) = abrackets (text "cstr" <+> pp c)
    pp t@(TpltType _ vars dict specs body) =
        text "template"
        <+> abrackets (sepBy comma $ map ppTpltArg vars)
        <+> abrackets (sepBy comma $ map pp specs)
        <+> pp body
        <+> text "environment:" $+$ nest 4 (pp dict)
    pp (TVar (VarName _ v)) = ppVarId v
    pp (TyLit lit) = pp lit
    pp t@TType = text (show t)
    pp t@KType = text (show t)
    pp t@(DType {}) = text (show t)
    pp Void = text "void"
    pp t@(StmtType {}) = text (show t)
    pp (CType s t d szs) = pp s <+> pp t <> brackets (brackets (pp d)) <> parens (sepBy comma $ map pp szs)
    pp (PrimType p) = pp p
    pp Public = text "public"
    pp (Private d k) = pp d
    pp t@(SysPush {}) = text (show t)
    pp t@(SysRet {}) = text (show t)
    pp t@(SysRef {}) = text (show t)
    pp t@(SysCRef {}) = text (show t)

deriving instance Show Type
deriving instance Data Type
deriving instance Eq Type  
deriving instance Ord Type

data TypeClass
    = KindStarC -- type of kinds
    | KindC -- kinds
    | DomainC -- for typed domains
    | TypeStarC -- type of types
    | TypeC -- regular type (dimensions included)
    | SysC -- system call parameters
  deriving (Read,Show,Data,Typeable,Eq,Ord)

typeClass :: Type -> TypeClass
typeClass TType = TypeStarC
typeClass KType = KindStarC
typeClass (DType _) = KindC
typeClass Public = DomainC
typeClass (Private _ _) = DomainC
typeClass (TVar (VarName t v)) | typeClass t == KindC = DomainC -- domain variables
                               | typeClass t == TypeStarC = TypeC -- type variables
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

instance PP StmtClass where
    pp = text . show

instance Vars StmtClass where
    traverseVars f c = return c
  
instance PP [Type] where
    pp = hcat . map pp
  
instance Vars [Type] where
    traverseVars f xs = mapM f xs
  
instance Vars Type where
  traverseVars f NoType = return NoType
  traverseVars f (ProcType pid p vs t stmts) = varsBlock $ do
      vs' <- inLHS $ mapM f vs
      t' <- f t
      stmts' <- f stmts
      return $ ProcType pid p vs' t' stmts'
  traverseVars f (StructType tid p as) = varsBlock $ do
      as' <- inLHS $ mapM f as
      return $ StructType tid p as'
  traverseVars f (TK c) = do
      c' <- f c
      return $ TK c'
  traverseVars f (TpltType tid vs d spes t) = varsBlock $ do
      vs' <- inLHS $ mapM f vs
      d' <- f d
      spes' <- mapM f spes
      t' <- f t
      return $ TpltType tid vs' d' spes' t'
  traverseVars f (TVar v) = do
      v' <- f v
      return $ TVar v'
  traverseVars f (TyLit l) = do
      l' <- f l
      return $ TyLit l'
  traverseVars f TType = return TType
  traverseVars f KType = return KType
  traverseVars f (DType d) = do
      d' <- mapM f d
      return $ DType d'
  traverseVars f Void = return Void
  traverseVars f (StmtType s) = do
      s' <- mapSetM f s
      return (StmtType s')
  traverseVars f (CType s t d z) = do
      s' <- f s
      t' <- f t
      d' <- f d
      z' <- mapM f z
      return $ CType s' t' d' z'
  traverseVars f (PrimType p) = do
      p' <- f p
      return $ PrimType p'
  traverseVars f Public = return Public
  traverseVars f (Private d k) = do
      d' <- f d
      k' <- f k
      return $ Private d' k'
  traverseVars f (SysPush t) = do
      t' <- f t
      return $ SysPush t'
  traverseVars f (SysRet t) = do
      t' <- f t
      return $ SysRet t'
  traverseVars f (SysRef t) = do
      t' <- f t
      return $ SysRef t'
  traverseVars f (SysCRef t) = do
      t' <- f t
      return $ SysCRef t'
  substL pl (TVar v) = let n = fmap (const ()) v in
      case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
          EqT -> Just n
          NeqT -> Nothing
  substL pl e = Nothing
  substR pa r =
      case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy (Proxy::Proxy (VarName VarIdentifier Type))) of
          EqT -> Just (TVar r)
          NeqT -> case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
              EqT -> Just r
              NeqT -> Nothing

data StmtClass
    -- | The execution of the statement may end because of reaching a return statement
    = StmtReturn
    -- | The execution of the statement may end because of reaching a break statement
    | StmtBreak
    -- | The execution of the statement may end because of reaching a continue statement
    | StmtContinue
    -- | The execution of the statement may end without reaching a return, break or continue statement
    | StmtFallthru
  deriving (Show,Data,Typeable,Eq,Ord)
    

isLoopStmtClass :: StmtClass -> Bool
isLoopStmtClass c = List.elem c [StmtBreak,StmtContinue]

isLoopBreakStmtClass :: StmtClass -> Bool
isLoopBreakStmtClass StmtBreak = True
isLoopBreakStmtClass (StmtReturn) = True
isLoopBreakStmtClass _ = False

isIterationStmtClass :: StmtClass -> Bool
isIterationStmtClass StmtContinue = True
isIterationStmtClass (StmtFallthru) = True
isIterationStmtClass c = False

hasStmtFallthru :: Set StmtClass -> Bool
hasStmtFallthru cs = not $ Set.null $ Set.filter isStmtFallthru cs

isStmtFallthru :: StmtClass -> Bool
isStmtFallthru (StmtFallthru) = True
isStmtFallthru c = False

data Typed a = Typed a Type
  deriving (Show,Data,Typeable,Functor,Eq,Ord)

instance PP a => PP (Typed a) where
    pp = pp . unTyped

instance Vars a => Vars (Typed a) where
    traverseVars f (Typed a t) = do
        a' <- f a
        t' <- inRHS $ f t
        return $ Typed a' t'

mapTyped :: (Type -> Type) -> Typed a -> Typed a
mapTyped f (Typed a t) = Typed a (f t)

instance Located loc => Located (Typed loc) where
    type (LocOf (Typed loc)) = LocOf loc
    loc = loc . unTyped
    updLoc (Typed x t) l = Typed (updLoc x l) t
    
instance Location a => Location (Typed a) where
    locpos = locpos . unTyped
    noloc = Typed noloc NoType
    updpos (Typed a t) p = Typed (updpos a p) t

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
defCType t = CType Public t (indexExpr 0) []

-- integer types
primIntBounds :: PrimitiveDatatype () -> (Integer,Integer)
primIntBounds (DatatypeInt8 _)      = (toInteger (minBound :: Int8)  ,toInteger (maxBound :: Int8))
primIntBounds (DatatypeInt16 _)     = (toInteger (minBound :: Int16) ,toInteger (maxBound :: Int16))
primIntBounds (DatatypeInt32 _)     = (toInteger (minBound :: Int32) ,toInteger (maxBound :: Int32))
primIntBounds (DatatypeInt64 _)     = (toInteger (minBound :: Int64) ,toInteger (maxBound :: Int64))
primIntBounds (DatatypeInt _)       = (toInteger (minBound :: Int64) ,toInteger (maxBound :: Int64))
primIntBounds (DatatypeUint8 _)     = (toInteger (minBound :: Word8) ,toInteger (maxBound :: Word8))
primIntBounds (DatatypeUint16 _)    = (toInteger (minBound :: Word16),toInteger (maxBound :: Word16))
primIntBounds (DatatypeUint32 _)    = (toInteger (minBound :: Word32),toInteger (maxBound :: Word32))
primIntBounds (DatatypeUint64 _)    = (toInteger (minBound :: Word64),toInteger (maxBound :: Word64))
primIntBounds (DatatypeUint _)      = (toInteger (minBound :: Word64),toInteger (maxBound :: Word64))
primIntBounds (DatatypeXorUint8 _)  = (toInteger (minBound :: Word8) ,toInteger (maxBound :: Word8))
primIntBounds (DatatypeXorUint16 _) = (toInteger (minBound :: Word16),toInteger (maxBound :: Word16))
primIntBounds (DatatypeXorUint32 _) = (toInteger (minBound :: Word32),toInteger (maxBound :: Word32))
primIntBounds (DatatypeXorUint64 _) = (toInteger (minBound :: Word64),toInteger (maxBound :: Word64))
primIntBounds (DatatypeXorUint _)   = (toInteger (minBound :: Word64),toInteger (maxBound :: Word64))
primIntBounds _ = (0,-1) -- nonsensical bounds

primFloatBounds :: PrimitiveDatatype () -> (Double,Double)
primFloatBounds (DatatypeFloat _) = (-2.802597 * 10 ^^(-45),3.402823 * (10 ^^38))
primFloatBounds (DatatypeFloat32 _) = (-2.802597 * 10 ^^(-45),3.402823 * (10 ^^38))
primFloatBounds (DatatypeFloat64 _) = (-4.940656 * 10 ^^ (-324),1.797693 * (10 ^^308))
primFloatBounds _ = (0,-1) -- nonsensical bounds

indexExpr :: Word64 -> Expression iden Type
indexExpr i = LitPExpr index $ IntLit index $ toInteger i

bytes :: Type
bytes = CType Public (PrimType $ DatatypeUint8 ()) (indexExpr 1) []
index = PrimType $ DatatypeUint64 ()
int = PrimType $ DatatypeInt ()
uint = PrimType $ DatatypeUint ()
int8 = PrimType $ DatatypeInt8 ()
uint8 = PrimType $ DatatypeUint8 ()
int16 = PrimType $ DatatypeInt16 ()
uint16 = PrimType $ DatatypeUint16 ()
int32 = PrimType $ DatatypeInt32 ()
uint32 = PrimType $ DatatypeUint32 ()
int64 = PrimType $ DatatypeInt64 ()
uint64 = PrimType $ DatatypeUint64 ()
string = PrimType $ DatatypeString ()
bool = PrimType $ DatatypeBool ()
xoruint8 = PrimType $ DatatypeXorUint8 ()
xoruint16 = PrimType $ DatatypeXorUint16 ()
xoruint32 = PrimType $ DatatypeXorUint32 ()
xoruint64 = PrimType $ DatatypeXorUint64 ()
xoruint = PrimType $ DatatypeXorUint ()
float = PrimType $ DatatypeFloat ()
float32 = PrimType $ DatatypeFloat32 ()
float64 = PrimType $ DatatypeFloat64 ()

prims = [int,uint,int8,uint8,int16,uint16,int32,uint32,int64,uint64,string,bool,xoruint8,xoruint16,xoruint32,xoruint64,xoruint,float,float32,float64]

numerics = filter isNumericType prims


isPublicType :: Type -> Bool
isPublicType Public = True
isPublicType _ = False

typeTyVarId :: Type -> TyVarId
typeTyVarId (StructType i _ _) = i
typeTyVarId (ProcType i _ _ _ _) = i
typeTyVarId (TpltType i _ _ _ _) = i

instance Location Type where
    locpos = const noloc
    noloc = NoType
    updpos t p = t

exprTypes :: (Data iden,Data a) => Expression iden a -> [Type]
exprTypes = everything (++) (mkQ [] aux)
    where
    aux :: Type -> [Type]
    aux = (:[])

-- Left = type template
-- Right = procedure overload
type TIdentifier = Either (TypeName VarIdentifier ()) PIdentifier

ppStructAtt :: Attribute VarIdentifier Type -> Doc
ppStructAtt (Attribute _ t n) = pp t <+> pp n

ppTpltType :: TIdentifier -> Type -> Doc
ppTpltType (Left n) (TpltType _ vars _ specs body@(StructType {})) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ text "struct" <+> pp n <> abrackets (sepBy comma $ map pp specs) <+> braces (text "...")
ppTpltType (Right (Left n)) (TpltType _ vars _ [] body@(ProcType _ _ args ret stmts)) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ pp ret <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)
ppTpltType (Right (Right n)) (TpltType _ vars _ [] body@(ProcType _ _ args ret stmts)) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)
ppTpltType (Right (Left n)) (ProcType _ _ args ret stmts) =
        pp ret <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)
ppTpltType (Right (Right n)) (ProcType _ _ args ret stmts) =
        pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)

ppTpltArg :: VarName VarIdentifier Type -> Doc
ppTpltArg (VarName TType v) = text "type" <+> ppVarId v
ppTpltArg (VarName (DType Nothing) v) = text "domain" <+> ppVarId v
ppTpltArg (VarName (DType (Just k)) v) = text "domain" <+> ppVarId v <+> char ':' <+> pp k
ppTpltArg (VarName t v) | isIntType t = text "dim" <+> ppVarId v

ppVarId :: VarIdentifier -> Doc
ppVarId (VarIdentifier n Nothing) =  text n
ppVarId (VarIdentifier n (Just i)) = text n <> Pretty.int i

ppTpltApp :: TIdentifier -> [Type] -> Maybe Type -> Doc
ppTpltApp (Left n) args Nothing = text "struct" <+> pp n <> abrackets (sepBy comma $ map pp args)
ppTpltApp (Right (Left n)) args (Just ret) = pp ret <+> pp n <> parens (sepBy comma $ map pp args)
ppTpltApp (Right (Right n)) args (Just ret) = pp ret <+> pp n <> parens (sepBy comma $ map pp args)
    
getSubstsGeneric :: Location loc => TcM loc (SubstsGeneric loc)
getSubstsGeneric = do
    env <- State.get
    let es = Map.foldrWithKey (\k e m -> case entryValue e of { KnownExpression ex -> Map.insert (VarName () k) (Right ex) m; otherwise -> m}) Map.empty $ vars env
    let sst = Map.foldrWithKey (\k t m -> Map.insert k (Left t) m) Map.empty $ tSubsts $ tDict env
    let sse = Map.foldrWithKey (\k e m -> Map.insert k (Right e) m) Map.empty $ tValues $ tDict env
    return $ Map.unions [es,sst,sse]
    
ppSubstsGeneric :: SubstsGeneric loc -> Doc
ppSubstsGeneric xs = vcat $ map ppSub $ Map.toList xs
    where
    ppSub (VarName _ k,Left t) = ppVarId k <+> char '=' <+> pp t
    ppSub (VarName _ k,Right e) = ppVarId k <+> char '=' <+> pp e

ppSubstsType :: SubstsType -> Doc
ppSubstsType xs = vcat $ map ppSub $ Map.toList xs
    where
    ppSub (VarName _ k,t) = ppVarId k <+> char '=' <+> pp t

ppSubstsVal :: SubstsVal loc -> Doc
ppSubstsVal xs = vcat $ map ppSub $ Map.toList xs
    where
    ppSub (VarName _ k,e) = ppVarId k <+> char '=' <+> pp e

ppArrayRanges :: [ArrayProj] -> Doc
ppArrayRanges = sepBy comma . map pp

hsValToExpr :: Location loc => loc -> HsVal -> Expression VarIdentifier (Typed loc)
hsValToExpr l (HsInt8 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l int8)
hsValToExpr l (HsInt16 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l int16)
hsValToExpr l (HsInt32 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l int32)
hsValToExpr l (HsInt64 i) = LitPExpr t $ IntLit t $ toInteger i
    where t = (Typed l int64)
hsValToExpr l (HsLit lit) = LitPExpr t $ fmap (const t) lit
    where t = (Typed l $ TyLit lit)

data HsVal where
    HsInt8 :: Int8 -> HsVal
    HsInt16 :: Int16 -> HsVal
    HsInt32 :: Int32 -> HsVal
    HsInt64 :: Int64 -> HsVal
    HsUint8 :: Word8 -> HsVal
    HsUint16 :: Word16 -> HsVal
    HsUint32 :: Word32 -> HsVal
    HsUint64 :: Word64 -> HsVal
    HsFloat32 :: Float -> HsVal
    HsFloat64 :: Double -> HsVal
    HsBool :: Bool -> HsVal
    HsLit :: Literal () -> HsVal
    HsContinue :: HsVal
    HsBreak :: HsVal
    HsVoid :: HsVal
    HsSysPush :: HsVal -> HsVal
    HsSysRet :: HsVal -> HsVal
    HsSysRef :: HsVal -> HsVal
    HsSysCRef :: HsVal -> HsVal
  deriving (Data,Typeable,Show)

instance Vars HsVal where
    traverseVars f h = return h

instance PP HsVal where
    pp (HsInt8 i) = text (show i)
    pp (HsInt16 i) = text (show i)
    pp (HsInt32 i) = text (show i)
    pp (HsInt64 i) = text (show i)
    pp (HsUint8 i) = text (show i)
    pp (HsUint16 i) = text (show i)
    pp (HsUint32 i) = text (show i)
    pp (HsUint64 i) = text (show i)
    pp (HsFloat32 i) = text (show i)
    pp (HsFloat64 i) = text (show i)
    pp (HsBool b) = text (show b)
    pp (HsLit l) = pp l
    pp HsContinue = text "continue"
    pp HsBreak = text "break"
    pp HsVoid = text "void"
    pp (HsSysPush v) = pp v 
    pp (HsSysRet v) = text "__ret" <+> pp v
    pp (HsSysRef v) = text "__ref" <+> pp v
    pp (HsSysCRef v) = text "__cref" <+> pp v

instance Eq HsVal where
    (HsInt8 i1) == (HsInt8 i2) = i1 == i2
    (HsInt8 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt8 i2) = i1 == toInteger i2
    (HsInt16 i1) == (HsInt16 i2) = i1 == i2
    (HsInt16 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt16 i2) = i1 == toInteger i2
    (HsInt32 i1) == (HsInt32 i2) = i1 == i2
    (HsInt32 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt32 i2) = i1 == toInteger i2
    (HsInt64 i1) == (HsInt64 i2) = i1 == i2
    (HsInt64 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsInt64 i2) = i1 == toInteger i2
    (HsLit l1) == (HsLit l2) = l1 == l2
    (HsBool b1) == (HsBool b2) = b1 == b2
    (HsUint8 i1) == (HsUint8 i2) = i1 == i2
    (HsUint8 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint8 i2) = i1 == toInteger i2
    (HsUint16 i1) == (HsUint16 i2) = i1 == i2
    (HsUint16 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint16 i2) = i1 == toInteger i2
    (HsUint32 i1) == (HsUint32 i2) = i1 == i2
    (HsUint32 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint32 i2) = i1 == toInteger i2
    (HsUint64 i1) == (HsUint64 i2) = i1 == i2
    (HsUint64 i1) == (HsLit (IntLit _ i2)) = toInteger i1 == i2
    (HsLit (IntLit _ i1)) == (HsUint64 i2) = i1 == toInteger i2
    (HsFloat32 i1) == (HsFloat32 i2) = i1 == i2
    (HsFloat32 i1) == (HsLit (FloatLit _ i2)) = realToFrac i1 == i2
    (HsLit (FloatLit _ i1)) == (HsFloat32 i2) = i1 == realToFrac i2
    (HsFloat64 i1) == (HsFloat64 i2) = i1 == i2
    (HsFloat64 i1) == (HsLit (FloatLit _ i2)) = realToFrac i1 == i2
    (HsLit (FloatLit _ i1)) == (HsFloat64 i2) = i1 == realToFrac i2
    HsContinue == HsContinue = True
    HsBreak == HsBreak = True
    HsVoid == HsVoid = True
    (HsSysPush v1) == (HsSysPush v2) = v1 == v2
    (HsSysRet v1) == (HsSysRet v2) = v1 == v2
    (HsSysRef v1) == (HsSysRef v2) = v1 == v2
    (HsSysCRef v1) == (HsSysCRef v2) = v1 == v2
    v1 == v2 = False

instance Ord HsVal where
    compare (HsInt8 i1) (HsInt8 i2) = i1 `compare` i2
    compare (HsInt8 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt8 i2) = i1 `compare` toInteger i2
    compare (HsInt16 i1) (HsInt16 i2) = i1 `compare` i2
    compare (HsInt16 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt16 i2) = i1 `compare` toInteger i2
    compare (HsInt32 i1) (HsInt32 i2) = i1 `compare` i2
    compare (HsInt32 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt32 i2) = i1 `compare` toInteger i2
    compare (HsInt64 i1) (HsInt64 i2) = i1 `compare` i2
    compare (HsInt64 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsInt64 i2) = i1 `compare` toInteger i2
    compare (HsLit l1) (HsLit l2) = l1 `compare` l2
    compare (HsBool b1) (HsBool b2) = b1 `compare` b2
    compare (HsUint8 i1) (HsUint8 i2) = i1 `compare` i2
    compare (HsUint8 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint8 i2) = i1 `compare` toInteger i2
    compare (HsUint16 i1) (HsUint16 i2) = i1 `compare` i2
    compare (HsUint16 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint16 i2) = i1 `compare` toInteger i2
    compare (HsUint32 i1) (HsUint32 i2) = i1 `compare` i2
    compare (HsUint32 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint32 i2) = i1 `compare` toInteger i2
    compare (HsUint64 i1) (HsUint64 i2) = i1 `compare` i2
    compare (HsUint64 i1) (HsLit (IntLit _ i2)) = toInteger i1 `compare` i2
    compare (HsLit (IntLit _ i1)) (HsUint64 i2) = i1 `compare` toInteger i2
    compare (HsFloat32 i1) (HsFloat32 i2) = i1 `compare` i2
    compare (HsFloat32 i1) (HsLit (FloatLit _ i2)) = realToFrac i1 `compare` i2
    compare (HsLit (FloatLit _ i1)) (HsFloat32 i2) = i1 `compare` realToFrac i2
    compare (HsFloat64 i1) (HsFloat64 i2) = i1 `compare` i2
    compare (HsFloat64 i1) (HsLit (FloatLit _ i2)) = realToFrac i1 `compare` i2
    compare (HsLit (FloatLit _ i1)) (HsFloat64 i2) = i1 `compare` realToFrac i2
    compare HsContinue HsContinue = EQ
    compare HsBreak HsBreak = EQ
    compare HsVoid HsVoid = EQ
    compare (HsSysPush v1) (HsSysPush v2) = v1 `compare` v2
    compare (HsSysRet v1) (HsSysRet v2) = v1 `compare` v2
    compare (HsSysRef v1) (HsSysRef v2) = v1 `compare` v2
    compare (HsSysCRef v1) (HsSysCRef v2) = v1 `compare` v2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)




    