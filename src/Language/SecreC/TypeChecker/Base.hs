{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

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
import Data.Bifunctor

import Control.Applicative
import Control.Monad.State as State
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding ((<>))
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
    , operators :: Map (Op VarIdentifier ()) (Map TyVarId (EntryEnv loc)) -- ^ defined operators: name |-> procedure decl
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
   
varNameToType :: VarName VarIdentifier Type -> Type
varNameToType (VarName (SType k) n) = SecT $ SVar (VarName () n) k
varNameToType (VarName TType n) = ComplexT $ CVar $ VarName () n
varNameToType (VarName BType n) = BaseT $ BVar $ VarName () n
varNameToType (VarName t n) | isIntType t = IdxT $ RVariablePExpr t $ VarName t n 

type SecrecErrArr = SecrecError -> SecrecError

newtype TcM loc a = TcM { unTcM :: RWST SecrecErrArr () (TcEnv loc) SecrecM a }
    deriving (Functor,Applicative,Typeable,Monad,MonadIO,MonadState (TcEnv loc),MonadReader SecrecErrArr,MonadWriter (),MonadError SecrecError,MonadPlus,Alternative)

tcError :: Position -> TypecheckerErr -> TcM loc a
tcError pos msg = do
    f <- Reader.ask
    throwError $ f $ typecheckerError pos msg

tcWarn :: Position -> TypecheckerWarn -> TcM loc ()
tcWarn pos msg = TcM $ lift $ tell [TypecheckerWarning pos msg]

askErrorM :: TcM loc SecrecErrArr
askErrorM = Reader.ask

newErrorM :: TcM loc a -> TcM loc a
newErrorM (TcM m) = TcM $ RWS.withRWST (\f s -> (id,s)) m

addErrorM :: SecrecErrArr -> TcM loc a -> TcM loc a
addErrorM err (TcM m) = TcM $ RWS.withRWST (\f s -> (f . err,s)) m

-- | Map different locations over @TcM@ monad.
tcLocM :: (loc2 -> loc1) -> (loc1 -> loc2) -> TcM loc1 a -> TcM loc2 a
tcLocM f g m = do
    s2 <- get
    r2 <- ask
    (x,s1,w1) <- TcM $ lift $ runRWST (unTcM m) r2 (fmap f s2)
    put (fmap g s1)
    tell w1
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
    r <- ask
    s <- get
    (x,s',w') <- TcM $ lift $ runRWST (unTcM m) r s
    modify $ \env -> env { tyVarId = tyVarId s' }
    Writer.tell w'
    return x

runTcM :: Location loc => TcM loc a -> SecrecM a
runTcM m = liftM fst $ RWS.evalRWST (unTcM m) id emptyTcEnv

type PIdentifier = Either (ProcedureName VarIdentifier ()) (Op VarIdentifier ())

-- | A template constraint with a result type
data TCstr
    = TApp (TypeName VarIdentifier ()) [Type] -- ^ type template application
    | TDec (TypeName VarIdentifier ()) [Type] -- ^ type template declaration
    | PDec -- ^ procedure declaration
        PIdentifier -- procedure name
        [Type] -- procedure arguments
        Type -- return type
    | Equals Type Type -- ^ types equal
    | Coerces Type Type -- ^ types coercible
    | CoercesSec
        SecType -- security type
        SecType -- security type
        ComplexType -- complex type over which to perform classify
    | Coerces2 Type Type -- ^ bidirectional coercion
    | Unifies Type Type -- ^ type unification
    | SupportedPrint [Type] -- ^ can call tostring on the argument type
    | ProjectStruct DecType (AttributeName VarIdentifier ()) -- ^ struct type projection
    | ProjectMatrix ComplexType [ArrayProj] -- ^ matrix type projection
    | IsReturnStmt (Set StmtClass) Type (ProcedureDeclaration VarIdentifier Position) -- ^ is return statement
    | DelayedCstr
        TCstr -- a constraint
        (SecrecError -> SecrecError) -- an error message with updated context
--    | GetCBase -- ^ get the base of a complex type
--        Type
--    | SetCBase -- ^ set the base of a complex type
--        Type -- ^ compelx type
--        Type -- ^ new base
--    | Cast -- ^ type cast
--        Type -- ^ from
--        Type -- ^ to
--    | InheritedCstr Position TCstr
  deriving (Data,Typeable,Show)
  
instance Eq TCstr where
    (TApp n1 ts1) == (TApp n2 ts2) = n1 == n2 && ts1 == ts2
    (TDec n1 ts1) == (TDec n2 ts2) = n1 == n2 && ts1 == ts2
    (PDec n1 ts1 r1) == (PDec n2 ts2 r2) = n1 == n2 && ts1 == ts2 && r1 == r2
    (Equals x1 y1) == (Equals x2 y2) = x1 == x2 && y1 == y2
    (Coerces x1 y1) == (Coerces x2 y2) = x1 == x2 && y1 == y2
    (CoercesSec x1 y1 c1) == (CoercesSec x2 y2 c2) = x1 == x2 && y1 == y2 && c1 == c2
    (Coerces2 x1 y1) == (Coerces2 x2 y2) = x1 == x2 && y1 == y2
    (Unifies x1 y1) == (Unifies x2 y2) = x1 == x2 && y1 == y2
    (SupportedPrint x1) == (SupportedPrint x2) = x1 == x2
    (ProjectStruct x1 y1) == (ProjectStruct x2 y2) = x1 == x2 && y1 == y2
    (ProjectMatrix x1 y1) == (ProjectMatrix x2 y2) = x1 == x2 && y1 == y2
    (IsReturnStmt s1 x1 y1) == (IsReturnStmt s2 x2 y2) = x1 == x2 && y1 == y2
    (DelayedCstr c1 _) == (DelayedCstr c2 _) = c1 == c2
    x == y = False
    
instance Ord TCstr where
    compare (TApp n1 ts1) (TApp n2 ts2) = mconcat [n1 `compare` n2,ts1 `compare` ts2]
    compare (TDec n1 ts1) (TDec n2 ts2) = mconcat [n1 `compare` n2,ts1 `compare` ts2]
    compare (PDec n1 ts1 r1) (PDec n2 ts2 r2) = mconcat [n1 `compare` n2,ts1 `compare` ts2,r1 `compare` r2]
    compare (Equals x1 y1) (Equals x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (Coerces x1 y1) (Coerces x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (CoercesSec x1 y1 c1) (CoercesSec x2 y2 c2) = mconcat [x1 `compare` x2,y1 `compare` y2,c1 `compare` c2]
    compare (Coerces2 x1 y1) (Coerces2 x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (Unifies x1 y1) (Unifies x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (SupportedPrint x1) (SupportedPrint x2) = x1 `compare` x2
    compare (ProjectStruct x1 y1) (ProjectStruct x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (ProjectMatrix x1 y1) (ProjectMatrix x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (IsReturnStmt s1 x1 y1) (IsReturnStmt s2 x2 y2) = mconcat [s1 `compare` s2,x1 `compare` x2,y1 `compare` y2]
    compare (DelayedCstr c1 _) (DelayedCstr c2 _) = c1 `compare` c2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)

instance PP TCstr where
    pp (TApp n ts) = text "tapp" <+> pp n <+> sepBy space (map pp ts)
    pp (TDec n ts) = text "tdec" <+> pp n <+> sepBy space (map pp ts)
    pp (PDec n ts r) = text "pdec" <+> pp n <+> parens (sepBy comma (map pp ts)) <+> pp r
    pp (Equals t1 t2) = text "equals" <+> pp t1 <+> pp t2
    pp (Coerces t1 t2) = text "coerces" <+> pp t1 <+> pp t2
    pp (CoercesSec t1 t2 b) = text "coercessec" <+> pp t1 <+> pp t2 <+> pp b
    pp (Coerces2 t1 t2) = text "coerces2" <+> pp t1 <+> pp t2
    pp (Unifies t1 t2) = text "unifies" <+> pp t1 <+> pp t2
    pp (SupportedPrint ts) = text "print" <+> sepBy space (map pp ts)
    pp (ProjectStruct t a) = pp t <> char '.' <> pp a
    pp (ProjectMatrix t as) = pp t <> brackets (sepBy comma $ map pp as) 
    pp (IsReturnStmt cs t dec) = text "return" <+> (hcat $ map pp $ Set.toList cs) <+> pp t <+> pp dec
    pp (DelayedCstr c f) = text "delayed" <+> pp c
--    pp (Cast from to) = text "cast" <+> pp from <+> pp to
--    pp (InheritedCstr p c) = text "inherited from" <+> pp p <+> pp c
--    pp (GetCBase t) = text "getcbase" <+> pp t
--    pp (SetCBase t p) = text "setcbase" <+> pp t <+> pp p
    
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

indexExpr :: Word64 -> Expression iden Type
indexExpr i = LitPExpr (BaseT index) $ IntLit (BaseT index) $ toInteger i
    
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
    traverseVars f (Equals t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Equals t1' t2'
    traverseVars f (Coerces t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Coerces t1' t2'
    traverseVars f (CoercesSec t1 t2 b) = do
        t1' <- f t1
        t2' <- f t2
        b' <- f b
        return $ CoercesSec t1' t2' b'
    traverseVars f (Coerces2 t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Coerces2 t1' t2'
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
    traverseVars f (DelayedCstr c err) = do
        c' <- f c
        return $ DelayedCstr c' err
--    traverseVars f (Cast from to) = do
--        from' <- f from
--        to' <- f to
--        return $ Cast from' to'
--    traverseVars f (InheritedCstr p k) = do
--        p' <- f p
--        k' <- f k
--        return $ InheritedCstr p' k'
--    traverseVars f (GetCBase t) = do
--        t' <- f t
--        return $ GetCBase t'
--    traverseVars f (SetCBase t p) = do
--        t' <- f t
--        p' <- f p
--        return $ SetCBase t' p'

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

instance Functor TDict where
    fmap f dict = dict { tCstrs = Map.mapKeys (mapLoc f) (tCstrs dict)
                       , tValues = Map.map (fmap (fmap f)) (tValues dict) }

instance Monoid (TDict loc) where
    mempty = TDict Map.empty Map.empty Map.empty
    mappend (TDict u1 ss1 ess1) (TDict u2 ss2 ess2) = TDict (Map.unionWith (\mb1 mb2 -> maybe mb2 Just mb1) u1 u2) (ss1 `Map.union` ss2) (ess1 `Map.union` ess2)

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

tSolved :: TDict loc -> Map (Loc loc TCstr) Type
tSolved = Map.foldrWithKey (\k v m -> maybe m (\x -> Map.insert k x m) v) Map.empty . tCstrs

tUnsolved :: TDict loc -> [Loc loc TCstr]
tUnsolved = Map.keys . Map.filter isNothing . tCstrs

insertTDictCstr :: loc -> TCstr -> Maybe Type -> TDict loc -> TDict loc
insertTDictCstr l c res dict = dict { tCstrs = Map.insertWith (\mb1 mb2 -> maybe mb2 Just mb1) (Loc l c) res (tCstrs dict) }

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

instance PP VarIdentifier where
    pp = ppVarId

type TyVarId = Int

data SecType
    = Public -- ^ public domain
    | Private -- ^ private domain
        (DomainName VarIdentifier ()) -- ^ domain
        (KindName VarIdentifier ()) -- ^ kind
    | SVar (VarName VarIdentifier ()) SVarKind
  deriving (Typeable,Show,Data,Eq,Ord)

data SVarKind
    = AnyKind
    | PrivateKind (Maybe (KindName VarIdentifier ()))
  deriving (Typeable,Show,Data,Eq,Ord)

data DecType
    = ProcType -- ^ procedure type
        TyVarId -- ^ unique procedure declaration id
        Position
        [VarName VarIdentifier Type] -- typed procedure arguments
        Type -- return type
        [Statement VarIdentifier (Typed Position)] -- ^ the procedure's body
    | StructType -- ^ Struct type
            TyVarId -- ^ unique structure declaration id
            Position -- ^ location of the procedure declaration
            [Attribute VarIdentifier Type] -- ^ typed arguments
    | TpltType -- ^ Template type
            TyVarId -- ^ unique template declaration id
            [VarName VarIdentifier Type] -- ^ template variables
            (TDict Position) -- ^ template constraints depending on the variables
            [Type] -- ^ template specializations
            DecType -- ^ template's type
  deriving (Typeable,Show,Data,Eq,Ord)

data BaseType
    = TyPrim (PrimitiveDatatype ())
    | TyDec DecType
    | BVar (VarName VarIdentifier ())
  deriving (Typeable,Show,Data,Eq,Ord)

data ComplexType
    = CType -- ^ Compound SecreC type
        SecType -- ^ security type
        BaseType -- ^ data type
        (Expression VarIdentifier Type) -- ^ dimension (default = 0, i.e., scalars)
        [Expression VarIdentifier Type] -- ^ sizes for each dimension (dependent types?) -- NOTE: check bounds if size is statically known?
    | CVar (VarName VarIdentifier ())
    | Void -- ^ Empty type
    | TyLit -- ^ the most concrete type for a literal. a complex type because we may cast literals into arrays
           (Literal ()) -- ^ the literal itself
  deriving (Typeable,Show,Data,Eq,Ord)

data SysType
    = SysPush Type
    | SysRet Type
    | SysRef Type
    | SysCRef Type
  deriving (Typeable,Show,Data,Eq,Ord)

data Type
    = NoType -- ^ For locations with no associated type information
    | TK -- ^ the result of resolving a constraint
        TCstr -- ^ a constraint returning a type
    | TType -- ^ Type of complex types
    | DType -- ^ Type of declarations
    | BType -- ^ Type of base types
    | KType -- ^ Type of kinds
    | SType -- ^ Type of domains
        SVarKind -- ^ optional kind of the domain Left isPrivate
    | StmtType (Set StmtClass) -- ^ Type of a @Statement@
    | ComplexT ComplexType
    | BaseT BaseType
    | SecT SecType
    | DecT DecType
    | SysT SysType
    | IdxT (Expression VarIdentifier Type) -- for index expressions
  deriving (Typeable,Show,Data,Eq,Ord)

instance PP SecType where
    pp Public = text "public"
    pp (Private d k) = pp d
    pp (SVar (VarName _ v) _) = ppVarId v
instance PP DecType where
    pp t@(ProcType _ _ vars ret stmts) =
        ptext "procedure"
        <+> parens (sepBy comma $ map ppProcArg vars)
        <+> pp ret
        <+> pp stmts
      where ppProcArg (VarName t n) = pp t <+> pp n
    pp t@(StructType _ _ atts) = text "struct" <+> braces (sepBy (char ';') $ map ppStructAtt atts)
    pp t@(TpltType _ vars dict specs body) =
        text "template"
        <+> abrackets (sepBy comma $ map ppTpltArg vars)
        <+> abrackets (sepBy comma $ map pp specs)
        <+> pp body
        <+> text "environment:" $+$ nest 4 (pp dict)
instance PP BaseType where
    pp (TyPrim p) = pp p
    pp (TyDec d) = pp d
    pp (BVar (VarName _ v)) = ppVarId v
instance PP ComplexType where
    pp (TyLit lit) = pp lit
    pp Void = text "void"
    pp (CType s t d szs) = pp s <+> pp t <> brackets (brackets (pp d)) <> parens (sepBy comma $ map pp szs)
    pp (CVar (VarName _ v)) = ppVarId v
instance PP SysType where
    pp t@(SysPush {}) = text (show t)
    pp t@(SysRet {}) = text (show t)
    pp t@(SysRef {}) = text (show t)
    pp t@(SysCRef {}) = text (show t)

instance PP Type where
    pp t@NoType = text (show t)
    pp t@(TK c) = abrackets (text "cstr" <+> pp c)
    pp t@TType = text (show t)
    pp t@BType = text (show t)
    pp t@DType = text (show t)
    pp t@(SType {}) = text (show t)
    pp t@KType = text (show t)
    pp t@(StmtType {}) = text (show t)
    pp (BaseT b) = pp b
    pp (ComplexT c) = pp c
    pp (SecT s) = pp s
    pp (DecT d) = pp d
    pp (SysT s) = pp s
    pp (IdxT e) = pp e

data TypeClass
    = KindStarC -- type of kinds
    | KindC -- kinds
    | DomainC -- for typed domains
    | TypeStarC -- type of types
    | ExprC -- type of regular expressions (also for index expressions)
    | TypeC -- regular type
    | SysC -- system call parameters
    | DecC -- type of declarations
  deriving (Read,Show,Data,Typeable,Eq,Ord)

typeClass :: Type -> TypeClass
typeClass TType = TypeStarC
typeClass BType = TypeStarC
typeClass KType = KindStarC
typeClass (SType _) = KindC
typeClass (SecT _) = DomainC
typeClass (DecT _) = DecC
typeClass (SysT _) = SysC
typeClass (IdxT _) = ExprC
typeClass (ComplexT _) = TypeC
typeClass (BaseT _) = TypeC
typeClass t = error $ "no typeclass for " ++ show t

isBoolType :: Type -> Bool
isBoolType (BaseT b) = isBoolBaseType b
isBoolType _ = False

isBoolBaseType :: BaseType -> Bool
isBoolBaseType (TyPrim (DatatypeBool _)) = True
isBoolBaseType _ = False

isIntType :: Type -> Bool
isIntType (ComplexT (TyLit (IntLit _ i))) = True
isIntType (BaseT b) = isIntBaseType b
isIntType _ = False

isIntBaseType :: BaseType -> Bool
isIntBaseType (TyPrim p) = isIntPrimType p
isIntBaseType t = False

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
isFloatType (BaseT b) = isFloatBaseType b
isFloatType (ComplexT (TyLit (FloatLit _ f))) = True
isFloatType _ = False

isFloatBaseType :: BaseType -> Bool
isFloatBaseType (TyPrim p) = isFloatPrimType p
isFloatBaseType t = False

isFloatPrimType :: PrimitiveDatatype () -> Bool
isFloatPrimType (DatatypeFloat _) = True
isFloatPrimType (DatatypeFloat32   _) = True
isFloatPrimType (DatatypeFloat64   _) = True
isFloatPrimType t = False

isNumericType :: Type -> Bool
isNumericType t = isIntType t || isFloatType t

isNumericBaseType :: BaseType -> Bool
isNumericBaseType t = isIntBaseType t || isFloatBaseType t

instance PP StmtClass where
    pp = text . show

instance Vars StmtClass where
    traverseVars f c = return c
  
instance PP [Type] where
    pp = hcat . map pp
  
instance Vars [Type] where
    traverseVars f xs = mapM f xs
  
instance Vars SecType where
    traverseVars f Public = return Public
    traverseVars f (Private d k) = do
        d' <- f d
        k' <- f k
        return $ Private d' k'
    traverseVars f (SVar v k) = do
        v' <- f v
        k' <- f k
        return $ SVar v' k'
    substL pl (SVar v _) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> Just n
            NeqT -> Nothing
    substL pl e = Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
            EqT -> Just r
            NeqT -> Nothing

instance Vars DecType where
    traverseVars f (ProcType pid p vs t stmts) = varsBlock $ do
        vs' <- inLHS $ mapM f vs
        t' <- f t
        stmts' <- f stmts
        return $ ProcType pid p vs' t' stmts'
    traverseVars f (StructType tid p as) = varsBlock $ do
        as' <- inLHS $ mapM f as
        return $ StructType tid p as'
    traverseVars f (TpltType tid vs d spes t) = varsBlock $ do
        vs' <- inLHS $ mapM f vs
        d' <- f d
        spes' <- mapM f spes
        t' <- f t
        return $ TpltType tid vs' d' spes' t'
    
instance Vars BaseType where
    traverseVars f (TyPrim p) = do
        p' <- f p
        return $ TyPrim p'
    traverseVars f (TyDec d) = do
        d' <- f d
        return $ TyDec d'
    traverseVars f (BVar v) = do
        v' <- f v
        return $ BVar v'
    substL pl (BVar v) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> Just n
            NeqT -> Nothing
    substL pl e = Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
            EqT -> Just r
            NeqT -> Nothing

instance Vars ComplexType where
    traverseVars f (TyLit l) = do
        l' <- f l
        return $ TyLit l'
    traverseVars f (CType s t d z) = do
        s' <- f s
        t' <- f t
        d' <- f d
        z' <- mapM f z
        return $ CType s' t' d' z'
    traverseVars f (CVar v) = do
        v' <- f v
        return $ CVar v'
    traverseVars f Void = return Void
    substL pl (CVar v) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> Just n
            NeqT -> Nothing
    substL pl e = Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
            EqT -> Just r
            NeqT -> Nothing

instance Vars SysType where
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

instance Vars SVarKind where
    traverseVars f AnyKind = return AnyKind
    traverseVars f (PrivateKind k) = do
        k' <- f k
        return $ PrivateKind k'

secTypeKind :: SecType -> SVarKind
secTypeKind Public = AnyKind
secTypeKind (Private _ k) = PrivateKind $ Just k
secTypeKind (SVar v k) = k

instance PP SVarKind where
    pp AnyKind = text "any"
    pp (PrivateKind Nothing) = text "private"
    pp (PrivateKind (Just k)) = text "private" <+> pp k
    
instance Vars Type where
    traverseVars f NoType = return NoType
    traverseVars f (TK c) = do
        c' <- f c
        return $ TK c'
    traverseVars f TType = return TType
    traverseVars f DType = return DType
    traverseVars f BType = return BType
    traverseVars f KType = return KType
    traverseVars f (SType s) = do
        s' <- f s
        return $ SType s'
    traverseVars f (StmtType s) = do
        s' <- mapSetM f s
        return (StmtType s')
    traverseVars f (ComplexT c) = do
        c' <- f c
        return $ ComplexT c'
    traverseVars f (BaseT c) = do
        c' <- f c
        return $ BaseT c'
    traverseVars f (SecT c) = do
        c' <- f c
        return $ SecT c'
    traverseVars f (DecT c) = do
        c' <- f c
        return $ DecT c'
    traverseVars f (SysT c) = do
        c' <- f c
        return $ SysT c'
    traverseVars f (IdxT c) = do
        c' <- f c
        return $ IdxT c'
    substL pl (BaseT (BVar v)) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> Just n
            NeqT -> Nothing
    substL pl (SecT (SVar v _)) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> Just n
            NeqT -> Nothing
    substL pl (ComplexT (CVar v)) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> Just n
            NeqT -> Nothing
    substL pl e = Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy (Proxy::Proxy (VarName VarIdentifier Type))) of
            EqT -> Just $ varNameToType r
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

isPublicType :: Type -> Bool
isPublicType (SecT s) = isPublicSecType s
isPublicType _ = False

isPublicSecType :: SecType -> Bool
isPublicSecType Public = True
isPublicSecType _ = False

typeTyVarId :: DecType -> TyVarId
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

setBase b (CType s t d sz) = CType s b d sz

-- Left = type template
-- Right = procedure overload
type TIdentifier = Either (TypeName VarIdentifier ()) PIdentifier

ppStructAtt :: Attribute VarIdentifier Type -> Doc
ppStructAtt (Attribute _ t n) = pp t <+> pp n

ppTpltType :: TIdentifier -> Type -> Doc
ppTpltType n (DecT t) = ppTpltDecType n t

ppTpltDecType :: TIdentifier -> DecType -> Doc
ppTpltDecType (Left n) (TpltType _ vars _ specs body@(StructType {})) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ text "struct" <+> pp n <> abrackets (sepBy comma $ map pp specs) <+> braces (text "...")
ppTpltDecType (Right (Left n)) (TpltType _ vars _ [] body@(ProcType _ _ args ret stmts)) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ pp ret <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)
ppTpltDecType (Right (Right n)) (TpltType _ vars _ [] body@(ProcType _ _ args ret stmts)) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)
ppTpltDecType (Right (Left n)) (ProcType _ _ args ret stmts) =
        pp ret <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)
ppTpltDecType (Right (Right n)) (ProcType _ _ args ret stmts) =
        pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (pp stmts)

ppTpltArg :: VarName VarIdentifier Type -> Doc
ppTpltArg (VarName BType v) = text "type" <+> ppVarId v
ppTpltArg (VarName TType v) = text "type" <+> ppVarId v
ppTpltArg (VarName (SType AnyKind) v) = text "domain" <+> ppVarId v
ppTpltArg (VarName (SType (PrivateKind Nothing)) v) = text "domain" <+> ppVarId v
ppTpltArg (VarName (SType (PrivateKind (Just k))) v) = text "domain" <+> ppVarId v <+> char ':' <+> pp k
ppTpltArg (VarName t v) | isIntType t = text "dim" <+> ppVarId v

ppVarId :: VarIdentifier -> Doc
ppVarId (VarIdentifier n Nothing) =  text n
ppVarId (VarIdentifier n (Just i)) = text n <> Pretty.int i

ppTpltApp :: TIdentifier -> [Type] -> Maybe Type -> Doc
ppTpltApp (Left n) args Nothing = text "struct" <+> pp n <> abrackets (sepBy comma $ map pp args)
ppTpltApp (Right (Left n)) args (Just ret) = pp ret <+> pp n <> parens (sepBy comma $ map pp args)
ppTpltApp (Right (Right n)) args (Just ret) = pp ret <+> pp n <> parens (sepBy comma $ map pp args)
    
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

bytes :: ComplexType
bytes = CType Public (TyPrim $ DatatypeUint8 ()) (indexExpr 1) []
index = TyPrim $ DatatypeUint64 ()
int = TyPrim $ DatatypeInt ()
uint = TyPrim $ DatatypeUint ()
int8 = TyPrim $ DatatypeInt8 ()
uint8 = TyPrim $ DatatypeUint8 ()
int16 = TyPrim $ DatatypeInt16 ()
uint16 = TyPrim $ DatatypeUint16 ()
int32 = TyPrim $ DatatypeInt32 ()
uint32 = TyPrim $ DatatypeUint32 ()
int64 = TyPrim $ DatatypeInt64 ()
uint64 = TyPrim $ DatatypeUint64 ()
string = TyPrim $ DatatypeString ()
bool = TyPrim $ DatatypeBool ()
xoruint8 = TyPrim $ DatatypeXorUint8 ()
xoruint16 = TyPrim $ DatatypeXorUint16 ()
xoruint32 = TyPrim $ DatatypeXorUint32 ()
xoruint64 = TyPrim $ DatatypeXorUint64 ()
xoruint = TyPrim $ DatatypeXorUint ()
float = TyPrim $ DatatypeFloat ()
float32 = TyPrim $ DatatypeFloat32 ()
float64 = TyPrim $ DatatypeFloat64 ()

prims = [int,uint,int8,uint8,int16,uint16,int32,uint32,int64,uint64,string,bool,xoruint8,xoruint16,xoruint32,xoruint64,xoruint,float,float32,float64]

numerics = filter isNumericBaseType prims

defCType :: BaseType -> ComplexType
defCType t = CType Public t (indexExpr 0) []