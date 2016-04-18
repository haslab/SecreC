{-# LANGUAGE DeriveGeneric, Rank2Types, UndecidableInstances, DeriveFoldable, DeriveTraversable, FlexibleContexts, ConstraintKinds, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty as PP
import Language.SecreC.Vars

import Data.Foldable
import Data.IORef
import Data.Unique
import Data.Int
import Data.Word
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Generics hiding (Generic,GT,typeOf,typeRep)
import Data.Dynamic hiding (typeOf,typeRep)
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Bifunctor
import Data.Hashable
import Data.SBV (Symbolic)
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.Query as Graph

import GHC.Generics (Generic)

import Control.Applicative
import Control.Monad.State as State
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding ((<>))
import Control.Monad.Trans.RWS (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS as RWS
import Control.Monad.Except
import Control.Monad.Trans.Control

import Unsafe.Coerce

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as PP

import qualified Data.HashTable.Weak.IO as WeakHash

import System.IO.Unsafe
import qualified System.Mem.Weak.Map as WeakMap
import System.Mem.Weak.Exts as Weak
import System.Exit
import System.IO

-- warn for unused local variables

data IOCstr = IOCstr
    { kCstr :: TCstr
    , kStatus :: UniqRef TCstrStatus
    }
  deriving (Data,Typeable,Show)

instance Hashable IOCstr where
    hashWithSalt i k = hashWithSalt i (kCstr k)
  
instance Eq IOCstr where
    k1 == k2 = kStatus k1 == kStatus k2
instance Ord IOCstr where
    compare k1 k2 = compare (kStatus k1) (kStatus k2)

instance PP IOCstr where
    pp k = pp (ioCstrId k) <+> char '=' <+> pp (kCstr k)

data TCstrStatus
    = Unevaluated -- has never been evaluated
    | Evaluated ShowOrdDyn  -- has been evaluated
    | Erroneous -- has failed
        SecrecError -- failure error
  deriving (Data,Typeable,Show,Generic)

instance Hashable TCstrStatus

data Scope = GlobalScope | LocalScope
  deriving (Show,Read,Data,Typeable,Generic)

instance Hashable Scope

instance PP Scope where
    pp GlobalScope = text "global"
    pp LocalScope = text "local"

{-# NOINLINE globalEnv #-}
globalEnv :: IORef GlobalEnv
globalEnv = unsafePerformIO (newGlobalEnv >>= newIORef)

newGlobalEnv :: IO GlobalEnv
newGlobalEnv = do
    m <- WeakHash.newSized 1024
    iom <- WeakHash.newSized 512
    return $ GlobalEnv m iom 0

resetGlobalEnv :: IO ()
--resetGlobalEnv = newGlobalEnv >>= writeIORef globalEnv
--resetGlobalEnv = do
--    g <- readIORef globalEnv
--    writeIORef globalEnv $ g { tyVarId = 0 }
resetGlobalEnv = do
    g <- readIORef globalEnv
    deps <- WeakHash.newSized 1024
    iodeps <- WeakHash.newSized 512
    writeIORef globalEnv $ g { tDeps = deps, ioDeps = iodeps }

orWarn :: (MonadIO m,Location loc) => TcM loc m a -> TcM loc m (Maybe a)
orWarn m = (liftM Just m) `catchError` \e -> do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Map.singleton (loc e) $ Set.singleton $ ErrWarn e
--    liftIO $ putStrLn $ "warning... " ++ ppr e
    return Nothing

orWarn_ :: (MonadIO m,Location loc) => TcM loc m a -> TcM loc m ()
orWarn_ m = orWarn m >> return ()

type GIdentifier = Either VarIdentifier (Either (Either (ProcedureName VarIdentifier ()) (Op VarIdentifier ())) (TypeName VarIdentifier ()))

data GlobalEnv = GlobalEnv
    { tDeps :: WeakHash.BasicHashTable GIdentifier (WeakMap.WeakMap Unique IOCstr) -- variable dependencies
    , ioDeps :: WeakHash.BasicHashTable Unique (WeakMap.WeakMap Unique IOCstr) -- IOCstr dependencies
    , tyVarId :: TyVarId
    }

--varIdDeps :: VarIdentifier -> IO (Set IOCstr)
--varIdDeps v = do
--    g <- readIORef globalEnv
--    mb <- WeakHash.lookup (tDeps g) v
--    case mb of
--        Nothing -> return Set.empty
--        Just cs -> WeakMap.foldM (\xs (_,iok) -> return $ Set.insert iok xs) Set.empty cs

type Deps loc = Set (Loc loc IOCstr)

getModuleCount :: (Monad m) => TcM loc m Int
getModuleCount = liftM moduleCount State.get

data TcEnv loc = TcEnv {
      globalVars :: Map VarIdentifier (Bool,EntryEnv loc) -- ^ global variables: name |-> (isConst,type of the variable)
    , localVars  :: Map VarIdentifier (Bool,EntryEnv loc) -- ^ local variables: name |-> (isConst,type of the variable)
    , localFrees :: Set VarIdentifier -- ^ free internal const variables generated during typechecking
    , globalDeps :: Deps loc -- ^ global dependencies
    , localDeps :: Deps loc -- ^ local dependencies
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
--    , inTemplate :: Bool -- ^ @True@ if we are type checking the body of a template declaration
    , tDict :: [TDict loc] -- ^ A stack of dictionaries
    , openedCstrs :: [IOCstr] -- constraints being resolved, for dependency tracking
    , moduleCount :: Int
    , inTemplate :: Bool -- if typechecking inside a template, global constraints are delayed
    , globalConsts :: Map Identifier VarIdentifier -- mapping from declared const variables to unique internal const variables: consts have to be in SSA to guarantee the typechecker's correctness
    , localConsts :: Map Identifier VarIdentifier
    }

--withCstrDependencies :: Monad m => TcM loc m a -> TcM loc m a
--withCstrDependencies m = do
--    gr <- liftM (tCstrs . headNe . tDict) State.get
--    withDependencies (flattenIOCstrGraphSet gr) m
--
withDependencies :: Monad m => Set (Loc loc IOCstr) -> TcM loc m a -> TcM loc m a
withDependencies deps m = do
    env <- State.get
    State.modify $ \env -> env { localDeps = deps `Set.union` localDeps env }
    x <- m
    State.modify $ \env -> env { localDeps = localDeps env }
    return x

tcEnvMap :: (loc2 -> loc1) -> (loc1 -> loc2) -> TcEnv loc2 -> TcEnv loc1
tcEnvMap f g env = TcEnv
    { globalVars = fmap (\(x,y) -> (x,fmap f y)) $ globalVars env
    , localVars = fmap (\(x,y) -> (x,fmap f y)) $ localVars env
    , localFrees = localFrees env
    , globalDeps = Set.fromList $ map (mapLoc f) $ Set.toList $ globalDeps env
    , localDeps = Set.fromList $ map (mapLoc f) $ Set.toList $ localDeps env
    , kinds = fmap (fmap f) $ kinds env
    , domains = fmap (fmap f) $ domains env
    , operators = Map.map (Map.map (fmap f)) $ operators env
    , procedures = Map.map (Map.map (fmap f)) $ procedures env
    , structs = Map.map (\(x,y) -> (fmap f x,Map.map (fmap f) y)) $ structs env
    , tDict = fmap (fmap f) $ tDict env
    , openedCstrs = openedCstrs env
    , moduleCount = moduleCount env
    , inTemplate = inTemplate env
    , globalConsts = globalConsts env
    , localConsts = localConsts env
    }

type VarsId m a = Vars VarIdentifier m a
type VarsIdTcM loc m = (Typeable m,MonadIO m,MonadBaseControl IO m,VarsId (TcM loc m) loc,VarsId (TcM loc Symbolic) loc)

emptyTcEnv :: TcEnv loc
emptyTcEnv = TcEnv
    { globalVars = Map.empty
    , localVars = Map.empty
    , localFrees = Set.empty
    , globalDeps = Set.empty
    , localDeps = Set.empty
    , kinds = Map.empty
    , domains = Map.empty
    , operators = Map.empty
    , procedures = Map.empty
    , structs = Map.empty
    , tDict = []
    , openedCstrs = []
    , moduleCount = 0
    , inTemplate = False
    , globalConsts = Map.empty
    , localConsts = Map.empty
    }

data EntryEnv loc = EntryEnv {
      entryLoc :: loc -- ^ Location where the entry is defined
    , entryType :: Type -- ^ Type of the entry
    }
  deriving Functor
  

instance Location loc => Located (EntryEnv loc) where
    type LocOf (EntryEnv loc) = loc
    loc = entryLoc
    updLoc e l = e { entryLoc = l }
   
varNameToType :: VarName VarIdentifier Type -> Type
varNameToType (VarName (SType k) n) = SecT $ SVar n k
varNameToType (VarName TType n) = ComplexT $ CVar n
varNameToType (VarName BType n) = BaseT $ BVar n
varNameToType (VarName DType n) = DecT $ DVar n
varNameToType (VarName (VAType b sz) n) = VArrayT $ VAVar n b sz
varNameToType (VarName t n) | typeClass "varNameToType" t == TypeC = IdxT (RVariablePExpr t $ VarName t n)
varNameToType v = error $ "varNameToType " ++ show v

condVarNameToType :: Cond (VarName VarIdentifier Type) -> Type
condVarNameToType (Cond v c) = condType (varNameToType v) c

typeToVarName :: Type -> Maybe (VarName VarIdentifier Type)
typeToVarName (SecT (SVar n k)) = Just (VarName (SType k) n)
typeToVarName (ComplexT (CVar n)) = Just (VarName TType n)
typeToVarName (BaseT (BVar n)) = Just (VarName BType n)
typeToVarName (DecT (DVar n)) = Just (VarName DType n)
typeToVarName (VArrayT (VAVar n b sz)) = Just (VarName (VAType b sz) n)
typeToVarName (IdxT (RVariablePExpr _ (VarName t n))) | typeClass "typeToVarName" t == TypeC = Just (VarName t n)
typeToVarName _ = Nothing

typeToTypeName :: Type -> Maybe (TypeName VarIdentifier Type)
typeToTypeName t = case typeToVarName t of
    Just (VarName _ n) -> Just $ TypeName t n
    otherwise -> Nothing
    
typeToDomainName :: Type -> Maybe (DomainName VarIdentifier Type)
typeToDomainName t = case typeToVarName t of
    Just (VarName _ n) -> Just $ DomainName t n
    otherwise -> Nothing

type SecrecErrArr = SecrecError -> SecrecError

newtype TcM loc m a = TcM { unTcM :: RWST (Int,SecrecErrArr) () (TcEnv loc) (SecrecM m) a }
    deriving (Functor,Applicative,Typeable,Monad,MonadIO,MonadState (TcEnv loc),MonadReader (Int,SecrecErrArr),MonadWriter (),MonadError SecrecError,MonadPlus,Alternative)

localOptsTcM :: Monad m => (Options -> Options) -> TcM loc m a -> TcM loc m a
localOptsTcM f (TcM m) = TcM $ RWS.mapRWST (local f) m

mapTcM :: (m (Either SecrecError ((a,TcEnv loc,()),SecrecWarnings)) -> n (Either SecrecError ((b,TcEnv loc,()),SecrecWarnings)))
    -> TcM loc m a -> TcM loc n b
mapTcM f (TcM m) = TcM $ RWS.mapRWST (mapSecrecM f) m

instance MonadTrans (TcM loc) where
    lift m = TcM $ lift $ SecrecM $ lift $ liftM (\x -> Right (x,mempty)) m

askErrorM :: Monad m => TcM loc m SecrecErrArr
askErrorM = liftM snd $ Reader.ask

askErrorM' :: Monad m => TcM loc m (Int,SecrecErrArr)
askErrorM' = Reader.ask

newErrorM :: TcM loc m a -> TcM loc m a
newErrorM (TcM m) = TcM $ RWS.withRWST (\f s -> ((0,id),s)) m

addErrorM :: (MonadIO m,Location loc) => loc -> SecrecErrArr -> TcM loc m a -> TcM loc m a
addErrorM l err m = addErrorM' l (1,err) m

addErrorM' :: (MonadIO m,Location loc) => loc -> (Int,SecrecErrArr) -> TcM loc m a -> TcM loc m a
addErrorM' l (j,err) (TcM m) = do
    size <- liftM fst Reader.ask
    opts <- askOpts
    if (size + j) > constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "nested errors"
        else TcM $ RWS.withRWST (\(i,f) s -> ((i + j,f . err),s)) m

tcPos :: (Monad m,Location loc) => TcM Position m a -> TcM loc m a
tcPos = tcLocM (locpos) (updpos noloc)

tcPosVarsM :: (Monad m,Location loc) => VarsM iden (TcM Position m) a -> VarsM iden (TcM loc m) a
tcPosVarsM m = mapStateT (tcPos) m

-- | Map different locations over @TcM@ monad.
tcLocM :: Monad m => (loc2 -> loc1) -> (loc1 -> loc2) -> TcM loc1 m a -> TcM loc2 m a
tcLocM f g m = do
    s2 <- get
    r2 <- ask
    (x,s1,w1) <- TcM $ lift $ runRWST (unTcM m) r2 (tcEnvMap f g s2)
    put (tcEnvMap g f s1)
    tell w1
    return x

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: Monad m => TcM loc m a -> TcM loc m a
tcBlock m = do
    r <- ask
    s <- get
    (x,s',w') <- TcM $ lift $ runRWST (unTcM m) r s
    Writer.tell w'
    return x

tcLocal :: Monad m => TcM loc m a -> TcM loc m a
tcLocal m = do
    env <- State.get
    x <- m
    State.modify $ \e -> e { localConsts = localConsts env, localVars = localVars env, localDeps = localDeps env }
    return x

-- a new dictionary
newDict l msg = do
    opts <- TcM $ lift ask
    size <- liftM (length . tDict) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "dictionaries"
        else do
            State.modify $ \e -> e { tDict = mempty : tDict e }
--            liftIO $ putStrLn $ "newDict " ++ show msg ++ " " ++ show size

tcWith :: (VarsIdTcM loc m,Location loc) => loc -> String -> TcM loc m a -> TcM loc m (a,TDict loc)
tcWith l msg m = do
    newDict l $ "tcWith " ++ msg
    x <- m
    d <- liftM (head . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (x:xs) = xs

execTcM :: (MonadIO m,Location loc) => TcM loc m a -> (Int,SecrecErrArr) -> TcEnv loc -> SecrecM m (a,TcEnv loc)
execTcM m arr env = do
    (x,env',()) <- RWS.runRWST (unTcM m) arr env
    return (x,env')

runTcM :: (MonadIO m,Location loc) => TcM loc m a -> SecrecM m a
runTcM m = liftM fst $ RWS.evalRWST (unTcM m) (0,id) emptyTcEnv

-- flips errors whenever typechecking is expected to fail
failTcM :: (MonadIO m,Location loc) => loc -> TcM loc m a -> TcM loc m a
failTcM l m = do
    opts <- TcM $ lift Reader.ask
    if failTypechecker opts
        then catchError
            (m >> liftIO (die $ ppr $ GenericError (locpos l) $ text "Typechecking should have failed"))
            (\e -> liftIO (hPutStrLn stderr (ppr e) >> exitSuccess))
        else m

type PIdentifier = Either (ProcedureName VarIdentifier ()) (Op VarIdentifier Type)

-- | Does a constraint depend on global template, procedure or struct definitions?
-- I.e., can it be overloaded?
isGlobalCstr :: TCstr -> Bool
isGlobalCstr k = isCheckCstr k || isHypCstr k || everything (||) (mkQ False isGlobalTcCstr) k

isGlobalTcCstr :: TcCstr -> Bool
isGlobalTcCstr (TDec {}) = True
isGlobalTcCstr (PDec {}) = True
isGlobalTcCstr (SupportedPrint {}) = True
isGlobalTcCstr (MultipleSubstitutions {}) = True
isGlobalTcCstr _ = False

-- | A template constraint with a result type
data TcCstr
    = TDec -- ^ type template declaration
        (TypeName VarIdentifier ()) -- template name
        [(Type,IsVariadic)] -- template arguments
        DecType -- result
    | PDec -- ^ procedure declaration
        PIdentifier -- procedure name
        (Maybe [(Type,IsVariadic)]) -- template arguments
        [(Expression VarIdentifier Type,IsVariadic)] -- procedure arguments
        Type -- return type
        DecType -- result
        (Maybe [VarName VarIdentifier Type]) -- resulting coerced procedure arguments
    | Equals Type Type -- ^ types equal
    | Coerces -- ^ types coercible
        (Expression VarIdentifier Type)
        (VarName VarIdentifier Type)
    | CoercesSec
        (Expression VarIdentifier Type) -- source expression
        (VarName VarIdentifier Type) -- target variable where to store the resulting expression
    | Coerces2 -- ^ bidirectional coercion
        (Expression VarIdentifier Type)
        (Expression VarIdentifier Type)
        (VarName VarIdentifier Type)
        (VarName VarIdentifier Type) 
    | Coerces2Sec
        (Expression VarIdentifier Type)
        (Expression VarIdentifier Type)
        (VarName VarIdentifier Type) -- variable to store the 1st resulting expression
        (VarName VarIdentifier Type) -- variable to store the 2nd resulting expression
    | Unifies -- unification
        Type Type -- ^ type unification
    | UnifiesSizes [(SExpr VarIdentifier Type,IsVariadic)] [(SExpr VarIdentifier Type,IsVariadic)]
    | SupportedPrint
        [(Expression VarIdentifier Type,IsVariadic)] -- ^ can call tostring on the argument type
        [VarName VarIdentifier Type] -- resulting coerced procedure arguments
    | ProjectStruct -- ^ struct type projection
        BaseType (AttributeName VarIdentifier ()) 
        Type -- result
    | ProjectMatrix -- ^ matrix type projection
        Type [ArrayProj]
        Type -- result
    | IsReturnStmt (Set StmtClass) Type -- ^ is return statement
    | MultipleSubstitutions VarIdentifier [(Type,[TcCstr])]
    | MatchTypeDimension
        Type -- type
        [(SExpr VarIdentifier Type,IsVariadic)] -- sequence of sizes
    | IsValid -- check if an index condition is valid (this is mandatory: raises an error)
        (SCond VarIdentifier Type) -- condition
    | TypeBase Type BaseType
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

instance Hashable TcCstr
 
isTrivialTcCstr :: TcCstr -> Bool
isTrivialTcCstr (Equals t1 t2) = t1 == t2
isTrivialTcCstr (Coerces e v) = e == varExpr v
isTrivialTcCstr (CoercesSec e v) = e == varExpr v
isTrivialTcCstr (Unifies t1 t2) = t1 == t2
isTrivialTcCstr (IsValid c) = c == trueSCond
isTrivialTcCstr _ = False
 
-- | checks (raise warnings)
data CheckCstr
    = CheckAssertion
        (SCond VarIdentifier Type) -- condition
    | CheckEqual -- x == y
        (SExpr VarIdentifier Type) -- left expr
        (SExpr VarIdentifier Type) -- right expr
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

instance Hashable CheckCstr
 
isTrivialCheckCstr :: CheckCstr -> Bool
isTrivialCheckCstr (CheckAssertion c) = c == trueSCond
isTrivialCheckCstr (CheckEqual e1 e2) = e1 == e2
 
-- hypothesis (raises warnings)
data HypCstr
    = HypCondition -- c == True
        (SExpr VarIdentifier Type)
    | HypNotCondition -- c == False
        (SExpr VarIdentifier Type)
    | HypEqual -- e1 == e2
        (SExpr VarIdentifier Type)
        (SExpr VarIdentifier Type)
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

instance Hashable HypCstr
 
isTrivialHypCstr :: HypCstr -> Bool
isTrivialHypCstr (HypCondition c) = c == trueSCond
isTrivialHypCstr (HypNotCondition c) = c == falseSCond
isTrivialHypCstr (HypEqual e1 e2) = e1 == e2
 
isTcCstr :: TCstr -> Bool
isTcCstr (TcK {}) = True
isTcCstr (DelayedK k _) = isTcCstr k
isTcCstr (CheckK {}) = False
isTcCstr (HypK {}) = False

isCheckCstr :: TCstr -> Bool
isCheckCstr (CheckK {}) = True
isCheckCstr (DelayedK k _) = isCheckCstr k
isCheckCstr (HypK {}) = False
isCheckCstr (TcK {}) = False

isHypCstr :: TCstr -> Bool
isHypCstr (HypK {}) = True
isHypCstr (DelayedK k _) = isHypCstr k
isHypCstr _ = False

isTrivialCstr :: TCstr -> Bool
isTrivialCstr (TcK c) = isTrivialTcCstr c
isTrivialCstr (DelayedK c _) = isTrivialCstr c
isTrivialCstr (CheckK c) = isTrivialCheckCstr c
isTrivialCstr (HypK c) = isTrivialHypCstr c

data TCstr
    = TcK TcCstr
    | DelayedK
        TCstr -- a constraint
        (Int,SecrecErrArr) -- an error message with updated context
    | CheckK CheckCstr
    | HypK HypCstr
  deriving (Data,Typeable,Show,Generic)

instance Hashable TCstr where
    hashWithSalt i (TcK c) = hashWithSalt i c
    hashWithSalt i (DelayedK c _) = hashWithSalt i c
    hashWithSalt i (CheckK c) = hashWithSalt i c
    hashWithSalt i (HypK c) = hashWithSalt i c
 
instance Eq TCstr where
    (DelayedK c1 _) == (DelayedK c2 _) = c1 == c2
    (TcK x) == (TcK y) = x == y
    (HypK x) == (HypK y) = x == y
    (CheckK x) == (CheckK y) = x == y
    x == y = False
    
instance Ord TCstr where
    compare (DelayedK c1 _) (DelayedK c2 _) = c1 `compare` c2
    compare (TcK c1) (TcK c2) = compare c1 c2
    compare (HypK x) (HypK y) = compare x y
    compare (CheckK x) (CheckK y) = compare x y
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)

priorityTCstr :: TCstr -> TCstr -> Ordering
priorityTCstr (DelayedK c1 _) (DelayedK c2 _) = priorityTCstr c1 c2
priorityTCstr (TcK c1) (TcK c2) = priorityTcCstr c1 c2
priorityTCstr (HypK x) (HypK y) = compare x y
priorityTCstr (CheckK x) (CheckK y) = compare x y
priorityTCstr (TcK {}) y = LT
priorityTCstr x (TcK {}) = GT
priorityTCstr (HypK {}) y = LT
priorityTCstr x (HypK {}) = GT

priorityTcCstr :: TcCstr -> TcCstr -> Ordering
priorityTcCstr (isMultipleSubstitionsTcCstr -> True) (isMultipleSubstitionsTcCstr -> False) = GT
priorityTcCstr (isMultipleSubstitionsTcCstr -> False) (isMultipleSubstitionsTcCstr -> True) = LT
priorityTcCstr (isGlobalTcCstr -> True) (isGlobalTcCstr -> False) = GT
priorityTcCstr (isGlobalTcCstr -> False) (isGlobalTcCstr -> True) = LT
priorityTcCstr (isValidTcCstr -> True) (isValidTcCstr -> False) = GT
priorityTcCstr (isValidTcCstr -> False) (isValidTcCstr -> True) = LT
priorityTcCstr c1 c2 = compare c1 c2

isMultipleSubstitionsTcCstr (MultipleSubstitutions {}) = True
isMultipleSubstitionsTcCstr _ = False

isValidTcCstr (IsValid {}) = True
isValidTcCstr _ = False

ppExprTy e = pp e <+> text "::" <+> pp (loc e)
ppVarTy v = ppExprTy (varExpr v)

instance PP TcCstr where
    pp (TDec n ts x) = text "tdec" <+> pp n <+> sepBy space (map pp ts) <+> char '=' <+> pp x
    pp (PDec n specs ts r x Nothing) = pp r <+> pp n <+> abrackets (sepBy comma (map pp $ maybe [] id specs)) <+> parens (sepBy comma (map (ppVariadicArg ppExprTy) ts)) <+> char '=' <+> pp x
    pp (PDec n specs ts r x (Just xs)) = pp r <+> pp n <+> abrackets (sepBy comma (map pp $ maybe [] id specs)) <+> parens (sepBy comma (map (ppVariadicArg ppExprTy) ts)) <+> char '=' <+> pp x <+> parens (sepBy comma $ map ppExprTy xs)
    pp (Equals t1 t2) = text "equals" <+> pp t1 <+> pp t2
    pp (Coerces e1 v2) = text "coerces" <+> ppExprTy e1 <+> ppVarTy v2
    pp (CoercesSec e1 v2) = text "coercessec" <+> ppExprTy e1 <+> ppVarTy v2
    pp (Coerces2Sec e1 e2 v1 v2) = text "coerces2sec" <+> ppExprTy e1 <+> ppExprTy e2 <+> char '=' <+> ppVarTy v1 <+> ppVarTy v2
    pp (Coerces2 e1 e2 v1 v2) = text "coerces2" <+> ppExprTy e1 <+> ppExprTy e2 <+> char '=' <+> ppVarTy v1 <+> ppVarTy v2
    pp (Unifies t1 t2) = text "unifies" <+> pp t1 <+> pp t2
    pp (UnifiesSizes t1 t2) = text "unifiessizes" <+> pp t1 <+> pp t2
    pp (SupportedPrint ts xs) = text "print" <+> sepBy space (map pp ts) <+> sepBy space (map pp xs)
    pp (ProjectStruct t a x) = pp t <> char '.' <> pp a <+> char '=' <+> pp x
    pp (ProjectMatrix t as x) = pp t <> brackets (sepBy comma $ map pp as) <+> char '=' <+> pp x
    pp (IsReturnStmt cs t) = text "return" <+> (hcat $ map pp $ Set.toList cs) <+> pp t
    pp (MultipleSubstitutions v s) = text "multiplesubstitutions" <+> pp v <+> pp (map fst s)
    pp (MatchTypeDimension t d) = text "matchtypedimension" <+> pp t <+> pp d
    pp (IsValid c) = text "isvalid" <+> pp c
    pp (TypeBase t b) = text "typebase" <+> pp t <+> pp b

instance PP CheckCstr where
    pp (CheckAssertion c) = text "checkAssertion" <+> pp c
    pp (CheckEqual e1 e2) = text "checkEqual" <+> pp e1 <+> pp e2

instance PP HypCstr where
    pp (HypCondition c) = text "hypothesis" <+> pp c
    pp (HypNotCondition c) = text "hypothesis" <+> char '!' <> pp c
    pp (HypEqual e1 e2) = text "hypothesis" <+> pp e1 <+> text "==" <+> pp e2

instance PP TCstr where
    pp (DelayedK c f) = text "delayed" <+> pp c
    pp (TcK k) = pp k
    pp (CheckK c) = pp c
    pp (HypK h) = pp h
--    pp (ClusterK xs) = char 'C' <> braces (vcat $ map pp $ Set.toList xs)
--    pp (GraphK xs) = char 'G' <> braces (pp xs)

data ArrayProj
    = ArraySlice ArrayIndex ArrayIndex
    | ArrayIdx ArrayIndex
  deriving (Data,Typeable,Show,Generic)

instance Hashable ArrayProj
    
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
    
instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m ArrayProj where
    traverseVars f (ArraySlice i1 i2) = do
        i1' <- f i1
        i2' <- f i2
        return $ ArraySlice i1' i2'
    traverseVars f (ArrayIdx w) = do
        w' <- f w
        return $ ArrayIdx w'
    
instance PP [Type] where
    pp xs = brackets $ sepBy comma $ map pp xs
    
instance PP [(Type,IsVariadic)] where
    pp xs = parens $ sepBy comma $ map (ppVariadicArg pp) xs
    
instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m [Type] where
    traverseVars f xs = mapM f xs
    
data ArrayIndex
    = NoArrayIndex
    | DynArrayIndex (SExpr VarIdentifier Type)
  deriving (Data,Typeable,Show,Generic)
  
instance Hashable ArrayIndex

instance Eq ArrayIndex where
    NoArrayIndex == NoArrayIndex = True
    (DynArrayIndex e1) == (DynArrayIndex e2) = e1 == e2
    x == y = False
instance Ord ArrayIndex where
    compare NoArrayIndex NoArrayIndex = EQ
    compare (DynArrayIndex e1) (DynArrayIndex e2) = compare e1 e2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)
  
instance PP ArrayIndex where
    pp NoArrayIndex = PP.empty
    pp (DynArrayIndex e) = pp e
    
instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m ArrayIndex where
    traverseVars f NoArrayIndex = return NoArrayIndex
    traverseVars f (DynArrayIndex e) = do
        e' <- f e
        return $ DynArrayIndex e'

arrayIndexSExpr :: ArrayIndex -> SExpr VarIdentifier Type
arrayIndexSExpr (DynArrayIndex e) = e

indexExpr :: Word64 -> Expression iden Type
indexExpr i = LitPExpr (BaseT index) $ IntLit (BaseT index) $ toInteger i

indexSExpr :: Word64 -> SExpr iden Type
indexSExpr i = (indexExpr i)

trueSCond :: SCond iden Type
trueSCond = (LitPExpr (BaseT bool) $ BoolLit (BaseT bool) True)

falseSCond :: SCond iden Type
falseSCond = (LitPExpr (BaseT bool) $ BoolLit (BaseT bool) False)

indexSExprLoc :: Location loc => Word64 -> SExpr iden (Typed loc)
indexSExprLoc i = (fmap (Typed noloc) $ indexExpr i)
    
instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m TcCstr where
    traverseVars f (TDec n args x) = do
        n' <- f n
        args' <- mapM f args
        x' <- f x
        return $ TDec n' args' x'
    traverseVars f (PDec n ts args ret x xs) = do
        n' <- f n
        x' <- f x
        ts' <- mapM (mapM (mapFstM f)) ts
        args' <- mapM (mapFstM f) args
        ret' <- f ret
        xs' <- mapM (mapM f) xs
        return $ PDec n' ts' args' ret' x' xs'
    traverseVars f (Equals t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Equals t1' t2'
    traverseVars f (Coerces e1 v2) = do
        e1' <- f e1
        v2' <- f v2
        return $ Coerces e1' v2'
    traverseVars f (CoercesSec e1 e2) = do
        e1' <- f e1
        e2' <- f e2
        return $ CoercesSec e1' e2'
    traverseVars f (Coerces2 e1 e2 v1 v2) = do
        e1' <- f e1
        e2' <- f e2
        v1' <- f v1
        v2' <- f v2
        return $ Coerces2 e1' e2' v1' v2'
    traverseVars f (Coerces2Sec e1 e2 v1 v2) = do
        e1' <- f e1
        e2' <- f e2
        v1' <- f v1
        v2' <- f v2
        return $ Coerces2Sec e1' e2' v1' v2'
    traverseVars f (Unifies t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Unifies t1' t2'
    traverseVars f (UnifiesSizes t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ UnifiesSizes t1' t2'
    traverseVars f (SupportedPrint ts xs) = do
        ts' <- mapM f ts
        xs' <- mapM f xs
        return $ SupportedPrint ts' xs'
    traverseVars f (ProjectStruct t a x) = do
        t' <- f t
        a' <- f a
        x' <- f x
        return $ ProjectStruct t' a' x'
    traverseVars f (ProjectMatrix t is x) = do
        t' <- f t
        is' <- mapM f is
        x' <- f x
        return $ ProjectMatrix t' is' x'
    traverseVars f (IsReturnStmt cs t) = do
        cs' <- mapSetM f cs
        t' <- f t
        return $ IsReturnStmt cs' t'
    traverseVars f (MultipleSubstitutions v s) = do
        v' <- f v
        s' <- mapM f s
        return $ MultipleSubstitutions v' s'
    traverseVars f (MatchTypeDimension t d) = do
        t' <- f t
        d' <- f d
        return $ MatchTypeDimension t' d'
    traverseVars f (IsValid c) = do
        c' <- f c
        return $ IsValid c'
    traverseVars f (TypeBase t b) = do
        t' <- f t
        b' <- f b
        return $ TypeBase t' b'

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m CheckCstr where
    traverseVars f (CheckAssertion c) = do
        c' <- f c
        return $ CheckAssertion c'
    traverseVars f (CheckEqual c1 c2) = do
        c1' <- f c1
        c2' <- f c2
        return $ CheckEqual c1' c2'

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m HypCstr where
    traverseVars f (HypCondition c) = do
        c' <- f c
        return $ HypCondition c'
    traverseVars f (HypNotCondition c) = do
        c' <- f c
        return $ HypNotCondition c'
    traverseVars f (HypEqual e1 e2) = do
        e1' <- f e1
        e2' <- f e2
        return $ HypEqual e1' e2'

instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m TCstr where
    traverseVars f (DelayedK c err) = do
        c' <- f c
        return $ DelayedK c' err
    traverseVars f (TcK k) = do
        k' <- f k
        return $ TcK k'
    traverseVars f (CheckK k) = do
        k' <- f k
        return $ CheckK k'
    traverseVars f (HypK k) = do
        k' <- f k
        return $ HypK k'
--    traverseVars f (ClusterK xs) = do
--        xs' <- liftM Set.fromList $ mapM f $ Set.toList xs
--        return $ ClusterK xs'
--    traverseVars f (GraphK xs) = do
--        xs' <- f xs
--        return $ GraphK xs'

type IOCstrGraph loc = Gr (Loc loc IOCstr) ()

-- | Template constraint dictionary
-- a dictionary with a set of inferred constraints and resolved constraints
data TDict loc = TDict
    { tCstrs :: IOCstrGraph loc -- a list of constraints
    , tChoices :: Set Int -- set of choice constraints that have already been branched
    , tSubsts :: TSubsts -- variable substitions
    }
  deriving (Typeable,Eq,Data,Ord,Show,Generic)

instance Hashable loc => Hashable (TDict loc)

flattenIOCstrGraph :: IOCstrGraph loc -> [Loc loc IOCstr]
flattenIOCstrGraph = map snd . labNodes

flattenIOCstrGraphSet :: IOCstrGraph loc -> Set (Loc loc IOCstr)
flattenIOCstrGraphSet = Set.fromList . flattenIOCstrGraph

-- | mappings from variables to current substitution
type TSubsts = Map VarIdentifier Type

instance Functor TDict where
    fmap f dict = dict { tCstrs = nmap (mapLoc f) (tCstrs dict) }

instance Monoid (TDict loc) where
    mempty = TDict Graph.empty Set.empty Map.empty
    mappend (TDict u1 c1 ss1) (TDict u2 c2 ss2) = TDict (unionGr u1 u2) (Set.union c1 c2) (ss1 `Map.union` ss2)

--addCstrDeps :: (MonadIO m,VarsId m TCstr) => IOCstr -> m ()
--addCstrDeps iok = do
--    vs <- fvs (kCstr iok)
--    addDeps vs iok
--  where
--    addDeps :: (MonadIO m,VarsId m TCstr) => Set VarIdentifier -> IOCstr -> m ()
--    addDeps vs iok = do
--        g <- liftM tDeps $ liftIO $ readIORef globalEnv
--        liftIO $ forM_ vs $ \v -> do
--            mb <- WeakHash.lookup g v
--            m <- maybe (WeakMap.new >>= \m -> WeakHash.insertWithMkWeak g v m (MkWeak $ mkWeakKey m) >> return m) return mb
--            WeakMap.insertWithMkWeak m (uniqId $ kStatus iok) iok (MkWeak $ mkWeakKey $ kStatus iok)

ioCstrId :: IOCstr -> Int
ioCstrId = hashUnique . uniqId . kStatus

type IOCstrSubsts = Map Int IOCstr

newIOCstrSubst :: (GenVar VarIdentifier m,MonadIO m) => (forall b . Vars VarIdentifier m b => b -> VarsM VarIdentifier m b) -> IOCstr -> VarsM VarIdentifier (StateT IOCstrSubsts m) IOCstr
newIOCstrSubst f iok = do
    xs <- lift State.get
    case Map.lookup (ioCstrId iok) xs of
        Nothing -> do
            st <- liftIO $ readUniqRef $ kStatus iok
            c' <- liftVarsM $ f (kCstr iok)
            let st' = case st of
                        Evaluated t -> Evaluated t
                        otherwise -> Unevaluated
            iok' <- liftM (IOCstr c') $ liftIO $ newUniqRef st'
            lift $ State.put $ Map.insert (ioCstrId iok) iok' xs
            return iok'
        Just iok' -> return iok'

getIOCstrSubst :: Monad m => Int -> IOCstr -> StateT IOCstrSubsts m IOCstr
getIOCstrSubst i def = do
    xs <- State.get
    return $ maybe def id $ Map.lookup i xs

getIOCstrSubstId :: Monad m => Int -> StateT IOCstrSubsts m Int
getIOCstrSubstId i = do
    xs <- State.get
    return $ maybe i ioCstrId $ Map.lookup i xs

instance (Vars VarIdentifier m loc,MonadIO m) => Vars VarIdentifier m (IOCstrGraph loc) where
    traverseVars f gr = flip evalVarsMState(Map.empty::IOCstrSubsts) $ traverseVarsIOCstrGraph f gr

traverseVarsIOCstrGraph :: (GenVar VarIdentifier m,MonadIO m) => (forall b . Vars VarIdentifier m b => b -> VarsM VarIdentifier m b) -> IOCstrGraph loc -> VarsM VarIdentifier (StateT IOCstrSubsts m) (IOCstrGraph loc)
traverseVarsIOCstrGraph f gr = do
        forM_ (labNodes gr) $ \(i,x) -> newIOCstrSubst f (unLoc x)
        mapGrM mapNode gr
      where
        mapNode ctx@(ins,nid,Loc l n,outs) = do
            n' <- lift $ getIOCstrSubst nid n
            ins' <- mapM (\(x,y) -> liftM (x,) $ lift $ getIOCstrSubstId y) ins
            outs' <- mapM (\(x,y) -> liftM (x,) $ lift $ getIOCstrSubstId y) outs
            return (ins',ioCstrId n',Loc l n',outs')      

evalVarsMState :: Monad m => VarsM iden (StateT st m) a -> st -> VarsM iden m a
evalVarsMState varsm st = mapStateT (\m -> evalStateT m st) varsm

liftVarsM :: (Monad m,MonadTrans t,Vars iden m a) => VarsM iden m a -> VarsM iden (t m) a
liftVarsM m = mapStateT (lift) m

instance (Location loc,MonadIO m,Vars VarIdentifier m loc) => Vars VarIdentifier m (TDict loc) where
    traverseVars f (TDict cstrs choices substs) = flip evalVarsMState (Map.empty::IOCstrSubsts) $ do
        cstrs' <- traverseVarsIOCstrGraph f cstrs
        choices' <- lift $ mapSetM getIOCstrSubstId choices
        substs' <- liftVarsM $ liftM Map.fromList $ mapM (\(x,y) -> do { x' <- f x; y' <- f y; return (x',y') }) $ Map.toList substs
        return $ TDict cstrs' choices' substs'

instance (Vars VarIdentifier m loc,Vars VarIdentifier m a) => Vars VarIdentifier m (Loc loc a) where
    traverseVars f (Loc l a) = do
        l' <- f l
        a' <- f a
        return $ Loc l' a'

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m IOCstr where
    traverseVars f (IOCstr k ref) = do
        k' <- f k
        ref' <- liftIO $ readUniqRef ref >>= newUniqRef
        return $ IOCstr k' ref'

-- we only need to fetch the head
getTSubsts :: (Monad m,Location loc) => TcM loc m TSubsts
getTSubsts = do
    env <- State.get
    return $ tSubsts $ mconcat $ tDict env

newTyVarId :: MonadIO m => m TyVarId
newTyVarId = liftIO $ atomicModifyIORef' globalEnv $ \g -> (g { tyVarId = succ (tyVarId g) },tyVarId g)

freshVarId :: MonadIO m => Identifier -> Maybe Doc -> m VarIdentifier
freshVarId n doc = do
    i <- newTyVarId
    let v = VarIdentifier n (Just i) False doc
    return v

uniqVarId :: MonadIO m => Identifier -> Maybe Doc -> TcM loc m VarIdentifier
uniqVarId n doc = do
    v <- freshVarId n doc
    addFree v
    return v
    
addFree n = modify $ \env -> env { localFrees = Set.insert n (localFrees env) }

instance PP (TDict loc) where
    pp dict = text "Constraints:" $+$ nest 4 (ppGr pp (const PP.empty) $ tCstrs dict)
          $+$ text "Substitutions:" $+$ nest 4 (ppTSubsts (tSubsts dict))

ppConstraints :: MonadIO m => TDict loc -> TcM loc m Doc
ppConstraints d = do
    let ppK (Loc l c) = do
        s <- liftIO $ readUniqRef $ kStatus c
        let pre = pp c
        case s of
            Evaluated t -> return $ pre <+> char '=' <+> text (show t)
            Unevaluated -> return $ pre
            Erroneous err -> return $ pre <+> char '=' <+> if isHaltError err then text "HALT" else text "ERROR"
    ss <- ppGrM ppK (const $ return PP.empty) (tCstrs d)
    return ss

data VarIdentifier = VarIdentifier
        { varIdBase :: Identifier
        , varIdUniq :: Maybe TyVarId
        , varIdTok :: Bool -- if the variable is a token (not to be resolved) (only used for comparisons)
        , varIdPretty :: Maybe Doc -- for free variables introduced by typechecking
        }
    deriving (Typeable,Data,Show)

instance Eq VarIdentifier where
    v1 == v2 = varIdBase v1 == varIdBase v2 && varIdUniq v1 == varIdUniq v2
instance Ord VarIdentifier where
    compare v1 v2 = mconcat [varIdBase v1 `compare` varIdBase v2,varIdUniq v1 `compare` varIdUniq v2]

varTok :: VarName VarIdentifier loc -> Bool
varTok (VarName _ n) = varIdTok n

mkVarId :: Identifier -> VarIdentifier
mkVarId s = VarIdentifier s Nothing False Nothing

instance PP VarIdentifier where
    pp v = case varIdPretty v of
        Just s -> ppVarId v <> char '#' <> s
        Nothing -> ppVarId v
      where
        ppVarId (VarIdentifier n Nothing _ _) = text n
        ppVarId (VarIdentifier n (Just i) _ _) = text n <> char '_' <> PP.int i

type TyVarId = Int

secTypeKind :: SecType -> SVarKind
secTypeKind Public = AnyKind
secTypeKind (Private _ k) = PrivateKind $ Just k
secTypeKind (SVar _ k) = k

data SecType
    = Public -- ^ public domain
    | Private -- ^ private domain
        (DomainName VarIdentifier ()) -- ^ domain
        (KindName VarIdentifier ()) -- ^ kind
    | SVar VarIdentifier SVarKind
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Hashable SecType

data SVarKind
    = AnyKind
    | PrivateKind (Maybe (KindName VarIdentifier ()))
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Hashable SVarKind

data DecType
    = ProcType -- ^ procedure type
--        TyVarId -- ^ unique procedure declaration id
        Position
        PIdentifier
        [(Bool,Cond (VarName VarIdentifier Type),IsVariadic)] -- typed procedure arguments
        Type -- return type
        [Statement VarIdentifier (Typed Position)] -- ^ the procedure's body
        ProcClass -- the type of procedure
    | StructType -- ^ Struct type
--        TyVarId -- ^ unique structure declaration id
        Position -- ^ location of the procedure declaration
        SIdentifier
        [Cond (Attribute VarIdentifier Type)] -- ^ typed arguments
    | DecType -- ^ top-level declaration (used for template declaration and also for non-templates to store substitutions)
        TyVarId -- ^ unique template declaration id
        Bool -- is a recursive invocation
        [(Cond (VarName VarIdentifier Type),IsVariadic)] -- ^ template variables
        (TDict Position) -- ^ constraints for the header
        (Set VarIdentifier) -- set of free internal constant variables generated when typechecking the template
        (TDict Position) -- ^ constraints for the template
        (Set VarIdentifier) -- set of free internal constant variables generated when typechecking the template
        [(Type,IsVariadic)] -- ^ template specializations
        DecType -- ^ template's type
    | DVar -- declaration variable
        VarIdentifier
  deriving (Typeable,Show,Data,Generic)

isTemplateDecType :: DecType -> Bool
isTemplateDecType (DecType _ _ ts _ _ _ _ specs _) = not (null ts && null specs)
isTemplateDecType _ = False

isNonRecursiveDecType :: DecType -> Bool
isNonRecursiveDecType (DecType i _ _ _ _ _ _ _ d) = not $ everything (||) (mkQ False aux) d
    where
    aux :: DecType -> Bool
    aux (DecType j True _ _ _ _ _ _ _) = i == j
    aux d = False
isNonRecursiveDecType d = False

instance Hashable DecType

instance Eq DecType where
    (DVar v1) == (DVar v2) = v1 == v2
    x == y = decTypeTyVarId x == decTypeTyVarId y
instance Ord DecType where
    compare (DVar v1) (DVar v2) = compare v1 v2
    compare x y = compare (decTypeTyVarId x) (decTypeTyVarId y)

data Cond a = Cond a (Maybe (SCond VarIdentifier Type))
  deriving (Typeable,Show,Data,Eq,Ord,Functor,Generic)

hasCond :: Cond a -> Bool
hasCond (Cond _ Nothing) = False
hasCond (Cond _ (Just _)) = True

instance Hashable a => Hashable (Cond a)

unCond :: Cond a -> a
unCond (Cond x c) = x

instance PP a => PP (Cond a) where
    pp = ppCond pp

ppCond :: (a -> Doc) -> Cond a -> Doc
ppCond f (Cond t Nothing) = f t
ppCond f (Cond t (Just c)) = f t <+> braces (pp c)

instance (MonadIO m,Vars VarIdentifier m a) => Vars VarIdentifier m (Cond a) where
    traverseVars f (Cond t e) = do
        t' <- f t
        e' <- inRHS $ f e
        return $ Cond t' e'

data BaseType
    = TyPrim Prim
    | TApp SIdentifier [(Type,IsVariadic)] DecType
    | BVar VarIdentifier
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Hashable BaseType

type SExpr iden loc = (Expression iden loc)
type SCond iden loc = (Expression iden loc)

data ComplexType
    = CType -- ^ Compound SecreC type
        SecType -- ^ security type
        BaseType -- ^ data type
        (SExpr VarIdentifier Type) -- ^ dimension (default = 0, i.e., scalars)
    | CVar VarIdentifier
    | Void -- ^ Empty type
    | TyLit -- ^ the most concrete type for a literal. a complex type because we may cast literals into arrays
           (Literal ()) -- ^ the literal itself
    | ArrayLit -- ^ a concrete array
        [SExpr VarIdentifier Type]
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Hashable ComplexType

data SysType
    = SysPush Type
    | SysRet Type
    | SysRef Type
    | SysCRef Type
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Hashable SysType

data Type
    = NoType String -- ^ For locations with no associated type information
    | TType -- ^ Type of complex types
    | DType -- ^ Type of declarations
    | BType -- ^ Type of base types
    | KType -- ^ Type of kinds
    | VAType Type (SExpr VarIdentifier Type) -- ^ Type of array types
    | SType -- ^ Type of domains
        SVarKind -- ^ optional kind of the domain Left isPrivate
    | StmtType (Set StmtClass) -- ^ Type of a @Statement@
    | ComplexT ComplexType
    | BaseT BaseType
    | SecT SecType
    | DecT DecType
    | SysT SysType
    | VArrayT VArrayType -- for variadic array types
    | IdxT (SExpr VarIdentifier Type) -- for index expressions
    | CondType Type (SCond VarIdentifier Type) -- a type with an invariant
  deriving (Typeable,Show,Data,Eq,Ord,Generic)
  
instance Hashable Type

-- | Type arrays
data VArrayType
    = VAVal -- a type array value
        [Type] -- array elements
        Type -- type of array elements
    | VAVar VarIdentifier Type (SExpr VarIdentifier Type) -- a type array variable
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Hashable VArrayType

vArraySize :: VArrayType -> SExpr VarIdentifier Type
vArraySize (VAVal xs _) = indexSExpr $ toEnum $ length xs
vArraySize (VAVar _ _ sz) = sz

tyOf :: Type -> Type
tyOf (IdxT _) = TType
tyOf (SecT s) = SType (secTypeKind s)
tyOf (ComplexT _) = TType
tyOf (BaseT _) = BType
tyOf (DecT _) = DType
tyOf (VArrayT (VAVal ts b)) = VAType b (indexSExpr $ toEnum $ length ts)
tyOf (VArrayT (VAVar v b sz)) = VAType b sz
tyOf (CondType t _) = tyOf t
tyOf t = error $ "unknown type for " ++ ppr t

condType :: Type -> Maybe (SCond VarIdentifier Type) -> Type
condType t Nothing = t
condType t (Just c) = CondType t c

ppOf a b = a <+> text "::" <+> b
ppTyped (a,b) = pp a `ppOf` pp b
ppFrees xs = text "Free variables:" <+> sepBy comma (map pp $ Set.toList xs) 

instance PP VArrayType where
    pp (VAVal ts b) = brackets $ sepBy comma (map pp ts) <+> text "::" <+> pp b <> text "[[1]]"
    pp (VAVar v b sz) = parens (pp v <+> text "::" <+> pp b <> text "[[1]]" <> parens (pp sz))

instance PP SecType where
    pp Public = text "public"
    pp (Private d k) = pp d
    pp (SVar v k) = parens (pp v <+> text "::" <+> pp k)
instance PP DecType where
    pp (DecType _ isrec vars hdict hfrees dict frees specs body@(StructType _ n atts)) =
        text "Frees:" <+> pp hfrees
        $+$ pp hdict
        $+$ text "Frees:" <+> pp frees
        $+$ pp dict
        $+$ text "template" <> abrackets (sepBy comma $ map (ppVariadicArg ppTpltArg) vars)
        $+$ text "struct" <+> pp n <> abrackets (sepBy comma $ map pp specs) <+> braces (text "...")
    pp (DecType _ isrec vars hdict hfrees dict frees [] body@(ProcType _ (Left n) args ret stmts _)) =
        text "Frees:" <+> pp hfrees
        $+$ pp hdict
        $+$ text "Frees:" <+> pp frees
        $+$ pp dict
        $+$ text "template" <> abrackets (sepBy comma $ map (ppVariadicArg ppTpltArg) vars)
        $+$ pp ret <+> pp n <> parens (sepBy comma $ map (\(isConst,Cond (VarName t n) c,isVariadic) -> ppConst isConst <+> ppVariadic (pp t) isVariadic <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (DecType _ isrec vars hdict hfrees dict frees [] body@(ProcType _ (Right n) args ret stmts _)) =
        text "Frees:" <+> pp hfrees
        $+$ pp hdict
        $+$ text "Frees:" <+> pp frees
        $+$ pp dict
        $+$ text "template" <> abrackets (sepBy comma $ map (ppVariadicArg ppTpltArg) vars)
        $+$ pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(isConst,Cond (VarName t n) c,isVariadic) -> ppConst isConst <+> ppVariadic (pp t) isVariadic <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (ProcType _ (Left n) args ret stmts _) =
            pp ret <+> pp n <> parens (sepBy comma $ map (\(isConst,Cond (VarName t n) c,isVariadic) -> ppConst isConst <+> ppVariadic (pp t) isVariadic <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (ProcType _ (Right n) args ret stmts _) =
            pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(isConst,Cond (VarName t n) c,isVariadic) -> ppConst isConst <+> ppVariadic (pp t) isVariadic <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (DVar v) = pp v
    pp (StructType _ n atts) = text "struct" <+> pp n <+> braces (text "...")
    pp d = error $ "pp: " ++ show d
instance PP BaseType where
    pp (TyPrim p) = pp p
    pp (TApp n ts d) = pp n <> abrackets (sepBy comma $ map (ppVariadicArg pp) ts)
    pp (BVar v) = pp v
instance PP ComplexType where
    pp (TyLit lit) = pp lit
    pp (ArrayLit es) = braces (sepBy comma $ map pp $ Foldable.toList es)
    pp Void = text "void"
    pp (CType s t d) = pp s <+> pp t <> brackets (brackets (pp d))
    pp (CVar v) = pp v
instance PP SysType where
    pp t@(SysPush {}) = text (show t)
    pp t@(SysRet {}) = text (show t)
    pp t@(SysRef {}) = text (show t)
    pp t@(SysCRef {}) = text (show t)

instance PP Type where
    pp t@(NoType msg) = text "no type"
    pp (VAType t sz) = parens $ pp t <> text "..." <> nonemptyParens (pp sz)
    pp t@TType = text "complex type"
    pp t@BType = text "base type"
    pp t@DType = text "declaration type"
    pp t@(SType k) = text "domain of kind" <+> pp k
    pp t@KType = text "kind type"
    pp t@(StmtType {}) = text (show t)
    pp (BaseT b) = pp b
    pp (ComplexT c) = pp c
    pp (SecT s) = pp s
    pp (DecT d) = pp d
    pp (SysT s) = pp s
    pp (IdxT e) = pp e
    pp (VArrayT a) = pp a
    pp (CondType t c) = ppCond pp (Cond t $ Just c)

isVATy :: Type -> Bool
isVATy (VAType {}) = True
isVATy (VArrayT {}) = True
isVATy _ = False

data TypeClass
    = KindStarC -- type of kinds
    | VArrayStarC TypeClass -- type of arrays types
    | KindC -- kinds
    | DomainC -- for typed domains
    | TypeStarC -- type of types
    | ExprC -- type of regular expressions (also for index expressions)
    | TypeC -- regular type
    | SysC -- system call parameters
    | DecC -- type of declarations
    | VArrayC TypeClass -- array type
  deriving (Read,Show,Data,Typeable,Eq,Ord)

instance PP TypeClass where
    pp KindStarC = text "kind star"
    pp (VArrayStarC t) = text "array star of" <+> pp t
    pp KindC = text "kind"
    pp DomainC = text "domain"
    pp TypeStarC = text "type star"
    pp ExprC = text "index expression"
    pp TypeC = text "complex type"
    pp SysC = text "system call parameter"
    pp DecC = text "declaration"
    pp (VArrayC t) = text "array" <+> pp t 

typeClass :: String -> Type -> TypeClass
typeClass msg (CondType t _) = typeClass msg t
typeClass msg TType = TypeStarC
typeClass msg (VAType b _) = VArrayStarC (typeClass msg b)
typeClass msg BType = TypeStarC
typeClass msg KType = KindStarC
typeClass msg (SType _) = KindC
typeClass msg (SecT _) = DomainC
typeClass msg (DecT _) = DecC
typeClass msg (SysT _) = SysC
typeClass msg (IdxT _) = ExprC
typeClass msg (VArrayT (VAVal ts b)) = VArrayC (typeClass msg b)
typeClass msg (VArrayT (VAVar v b sz)) = VArrayC (typeClass msg b)
typeClass msg (ComplexT _) = TypeC
typeClass msg (BaseT _) = TypeC
typeClass msg t = error $ msg ++ ": no typeclass for " ++ show t

isStruct :: DecType -> Bool
isStruct (DecType _ _ _ _ _ _ _ _ (StructType {})) = True
isStruct (StructType {}) = True
isStruct _ = False

isStructTemplate :: Type -> Bool
isStructTemplate (DecT (DecType _ _ _ _ _ _ _ _ (StructType {}))) = True
isStructTemplate _ = False

isVoid :: ComplexType -> Bool
isVoid Void = True
isVoid _ = False

isLitType :: Type -> Bool
isLitType (ComplexT c) = isLitCType c
isLitType _ = False

isLitCType :: ComplexType -> Bool
isLitCType (TyLit {}) = True
isLitCType (ArrayLit {}) = True
isLitCType _ = False

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

isIntPrimType :: Prim -> Bool
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
isIntPrimType t = False

isFloatType :: Type -> Bool
isFloatType (BaseT b) = isFloatBaseType b
isFloatType (ComplexT (TyLit (FloatLit _ f))) = True
isFloatType _ = False

isFloatBaseType :: BaseType -> Bool
isFloatBaseType (TyPrim p) = isFloatPrimType p
isFloatBaseType t = False

isFloatPrimType :: Prim -> Bool
isFloatPrimType (DatatypeFloat32   _) = True
isFloatPrimType (DatatypeFloat64   _) = True
isFloatPrimType t = False

isNumericType :: Type -> Bool
isNumericType t = isIntType t || isFloatType t

isNumericBaseType :: BaseType -> Bool
isNumericBaseType t = isIntBaseType t || isFloatBaseType t

isNumericPrimType :: Prim -> Bool
isNumericPrimType t = isIntPrimType t || isFloatPrimType t

instance PP StmtClass where
    pp = text . show

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m StmtClass where
    traverseVars f c = return c
  
instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m SecType where
    traverseVars f Public = return Public
    traverseVars f (Private d k) = do
        d' <- f d
        k' <- f k
        return $ Private d' k'
    traverseVars f (SVar v k) = do
        v' <- f v
        k' <- f k
        return $ SVar v' k'
    substL (SVar v _) = return $ Just v
    substL e = return $ Nothing

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m [TCstr] where
    traverseVars f xs = mapM f xs
    
instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m [TcCstr] where
    traverseVars f xs = mapM f xs

instance PP [TCstr] where
    pp xs = brackets (sepBy comma $ map pp xs)
    
instance PP [TcCstr] where
    pp xs = brackets (sepBy comma $ map pp xs)

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m ProcClass where
    traverseVars f PureFunc = return PureFunc
    traverseVars f (RWProc rs ws) = do
        rs' <- f rs
        ws' <- f ws
        return $ RWProc rs' ws'

instance PP ProcClass where
    pp PureFunc = text "function"
    pp (RWProc rs ws) = text "procedure" <+> pp rs <+> pp ws

instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m DecType where
    traverseVars f (ProcType p n vs t stmts c) = varsBlock $ do
        n' <- f n
        vs' <- inLHS $ mapM f vs
        t' <- f t
        stmts' <- f stmts
        c' <- f c
        return $ ProcType p n' vs' t' stmts' c'
    traverseVars f (StructType p n as) = varsBlock $ do
        n' <- f n
        as' <- inLHS $ mapM f as
        return $ StructType p n' as'
    traverseVars f (DecType tid isrec vs hd hfrees d frees spes t) = varsBlock $ do
        vs' <- inLHS $ mapM f vs
        hfrees' <- liftM Set.fromList $ mapM f $ Set.toList hfrees
        frees' <- liftM Set.fromList $ mapM f $ Set.toList frees
        hd' <- f hd
        d' <- f d
        spes' <- mapM f spes
        t' <- f t
        return $ DecType tid isrec vs' hd' hfrees' d' frees' spes' t'
    traverseVars f (DVar v) = do
        v' <- f v
        return $ DVar v'
    substL (DVar v) = return $ Just v
    substL _ = return Nothing
    
instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m BaseType where
    traverseVars f (TyPrim p) = do
        p' <- f p
        return $ TyPrim p'
    traverseVars f (TApp n ts d) = do
        n' <- f n
        ts' <- mapM f ts
        d' <- f d
        return $ TApp n' ts' d'
    traverseVars f (BVar v) = do
        v' <- f v
        return $ BVar v'
    substL (BVar v) = return $ Just v
    substL e = return Nothing
 
instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m VArrayType where
    traverseVars f (VAVal ts b) = do
        ts' <- f ts
        b' <- f b
        return $ VAVal ts' b'
    traverseVars f (VAVar v b sz) = do
        v' <- f v
        b' <- f b
        sz' <- f sz
        return $ VAVar v' b' sz'
    substL (VAVar v _ _) = return $ Just v
    substL e = return Nothing
 
instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m ComplexType where
    traverseVars f (TyLit l) = do
        l' <- f l
        return $ TyLit l'
    traverseVars f (ArrayLit l) = do
        l' <- mapM f l
        return $ ArrayLit l'
    traverseVars f (CType s t d) = do
        s' <- f s
        t' <- f t
        d' <- f d
        return $ CType s' t' d'
    traverseVars f (CVar v) = do
        v' <- f v
        return $ CVar v'
    traverseVars f Void = return Void
    substL (CVar v) = return $ Just v
    substL e = return Nothing

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m SysType where
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

instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m SVarKind where
    traverseVars f AnyKind = return AnyKind
    traverseVars f (PrivateKind k) = do
        k' <- f k
        return $ PrivateKind k'

instance PP SVarKind where
    pp AnyKind = text "*"
    pp (PrivateKind Nothing) = text "private *"
    pp (PrivateKind (Just k)) = text "private" <+> pp k
    
instance (GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m Type where
    traverseVars f (NoType x) = return (NoType x)
    traverseVars f TType = return TType
    traverseVars f (VAType t sz) = do
        t' <- f t
        sz' <- f sz
        return $ VAType t' sz'
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
    traverseVars f (VArrayT a) = do
        a' <- f a
        return $ VArrayT a'
    traverseVars f (CondType t c) = do
        t' <- f t
        c' <- f c
        return $ CondType t' c'
    substL (BaseT (BVar v)) = return $ Just v
    substL (SecT (SVar v _)) = return $ Just v
    substL (ComplexT (CVar v)) = return $ Just v
    substL (DecT (DVar v)) = return $ Just v
    substL (IdxT (RVariablePExpr _ v)) = return $ Just $ varNameId v
    substL (VArrayT (VAVar v _ _)) = return $ Just v
    substL e = return Nothing

data ProcClass
    -- | A pure function that does not read or write global variables
    = PureFunc
    -- | A procedure that reads and/or writes global variables
    | RWProc
        (Set VarIdentifier) -- read variables
        (Set VarIdentifier)  -- written variables
  deriving (Show,Data,Typeable,Eq,Ord,Generic)
instance Hashable ProcClass

data StmtClass
    -- | The execution of the statement may end because of reaching a return statement
    = StmtReturn
    -- | The execution of the statement may end because of reaching a break statement
    | StmtBreak
    -- | The execution of the statement may end because of reaching a continue statement
    | StmtContinue
    -- | The execution of the statement may end without reaching a return, break or continue statement
    | StmtFallthru
  deriving (Show,Data,Typeable,Eq,Ord,Generic) 
instance Hashable StmtClass

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
  deriving (Show,Data,Typeable,Functor,Eq,Ord,Generic)
instance Hashable a => Hashable (Typed a)

instance PP a => PP (Typed a) where
    pp = pp . unTyped

instance (MonadIO m,Vars VarIdentifier m a) => Vars VarIdentifier m (Typed a) where
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
    noloc = Typed noloc (NoType "noloc")
    updpos (Typed a t) p = Typed (updpos a p) t

notTyped :: String -> a -> Typed a
notTyped msg x = Typed x (NoType msg)

typed :: Typed a -> Type
typed (Typed _ t) = t

unTyped :: Typed a -> a
unTyped (Typed a t) = a

locType :: Typed Position -> Type
locType (Typed _ t) = t

typeLoc :: Type -> Position -> Typed Position
typeLoc t l = Typed l t

noTypeLoc :: Loc loc a -> Loc (Typed loc) a
noTypeLoc = mapLoc (flip Typed (NoType "noTypeLoc"))

isPublicType :: Type -> Bool
isPublicType (SecT s) = isPublicSecType s
isPublicType _ = False

isPublicSecType :: SecType -> Bool
isPublicSecType Public = True
isPublicSecType _ = False

decTypeTyVarId :: DecType -> Maybe TyVarId
decTypeTyVarId (StructType _ _ _) = Nothing
decTypeTyVarId (ProcType _ _ _ _ _ _) = Nothing
decTypeTyVarId (DecType i _ _ _ _ _ _ _ _) = Just i
decTypeTyVarId (DVar _) = Nothing

instance Location Type where
    locpos = const noloc
    noloc = NoType "noloc"
    updpos t p = t

instance Location a => Location (Cond a) where
    locpos = locpos . unCond
    noloc = Cond noloc Nothing
    updpos t p = t

exprTypes :: (Data iden,Data a) => Expression iden a -> [Type]
exprTypes = everything (++) (mkQ [] aux)
    where
    aux :: Type -> [Type]
    aux = (:[])

setBase b (CType s t d) = CType s b d

-- Left = type template
-- Right = procedure overload
type TIdentifier = Either SIdentifier PIdentifier

type SIdentifier = TypeName VarIdentifier ()

ppStructAtt :: Attribute VarIdentifier Type -> Doc
ppStructAtt (Attribute _ t n) = pp t <+> pp n

ppTpltArg :: Cond (VarName VarIdentifier Type) -> Doc
ppTpltArg = ppCond ppTpltArg'
    where
    ppTpltArg' :: VarName VarIdentifier Type -> Doc
    ppTpltArg' (VarName BType v) = text "type" <+> pp v
    ppTpltArg' (VarName (SType AnyKind) v) = text "domain" <+> pp v
    ppTpltArg' (VarName (SType (PrivateKind Nothing)) v) = text "domain" <+> pp v
    ppTpltArg' (VarName (SType (PrivateKind (Just k))) v) = text "domain" <+> pp v <+> char ':' <+> pp k
    ppTpltArg' (VarName t v) | isIntType t = text "dim" <+> pp v
    ppTpltArg' (VarName (VAType b sz) v) | isIntType b = text "dim..." <+> pp v
    ppTpltArg' (VarName (VAType BType sz) v) = text "type..." <+> pp v
    ppTpltArg' (VarName (VAType (SType _) sz) v) = text "domain..." <+> pp v
    ppTpltArg' v = error $ "ppTpltArg: " ++ ppr v ++ " " ++ ppr (loc v)
    
ppTSubsts :: TSubsts -> Doc
ppTSubsts xs = vcat $ map ppSub $ Map.toList xs
    where
    ppSub (k,IdxT e) = pp k <+> char '=' <+> ppExprTy e
    ppSub (k,t) = pp k <+> char '=' <+> pp t

ppArrayRanges :: [ArrayProj] -> Doc
ppArrayRanges = sepBy comma . map pp

-- integer types
primIntBounds :: Prim -> Maybe (Integer,Integer)
primIntBounds (DatatypeInt8 _)      = Just (toInteger (minBound :: Int8)  ,toInteger (maxBound :: Int8))
primIntBounds (DatatypeInt16 _)     = Just (toInteger (minBound :: Int16) ,toInteger (maxBound :: Int16))
primIntBounds (DatatypeInt32 _)     = Just (toInteger (minBound :: Int32) ,toInteger (maxBound :: Int32))
primIntBounds (DatatypeInt64 _)     = Just (toInteger (minBound :: Int64) ,toInteger (maxBound :: Int64))
primIntBounds (DatatypeUint8 _)     = Just (toInteger (minBound :: Word8) ,toInteger (maxBound :: Word8))
primIntBounds (DatatypeUint16 _)    = Just (toInteger (minBound :: Word16),toInteger (maxBound :: Word16))
primIntBounds (DatatypeUint32 _)    = Just (toInteger (minBound :: Word32),toInteger (maxBound :: Word32))
primIntBounds (DatatypeUint64 _)    = Just (toInteger (minBound :: Word64),toInteger (maxBound :: Word64))
primIntBounds (DatatypeXorUint8 _)  = Just (toInteger (minBound :: Word8) ,toInteger (maxBound :: Word8))
primIntBounds (DatatypeXorUint16 _) = Just (toInteger (minBound :: Word16),toInteger (maxBound :: Word16))
primIntBounds (DatatypeXorUint32 _) = Just (toInteger (minBound :: Word32),toInteger (maxBound :: Word32))
primIntBounds (DatatypeXorUint64 _) = Just (toInteger (minBound :: Word64),toInteger (maxBound :: Word64))
primIntBounds _ = Nothing

primFloatBounds :: Prim -> Maybe (Double,Double)
primFloatBounds (DatatypeFloat32 _) = Just (-2.802597 * 10 ^^(-45),3.402823 * (10 ^^38))
primFloatBounds (DatatypeFloat64 _) = Just (-4.940656 * 10 ^^ (-324),1.797693 * (10 ^^308))
primFloatBounds _ = Nothing

index = TyPrim $ DatatypeUint64 ()
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
float32 = TyPrim $ DatatypeFloat32 ()
float64 = TyPrim $ DatatypeFloat64 ()

prims = [int8,uint8,int16,uint16,int32,uint32,int64,uint64,string,bool,xoruint8,xoruint16,xoruint32,xoruint64,float32,float64]

numerics = filter isNumericBaseType prims

defCType :: BaseType -> ComplexType
defCType t = CType Public t (indexSExpr 0)

instance Hashable VarIdentifier where
    hashWithSalt i v = hashWithSalt (maybe i (i+) $ varIdUniq v) (varIdBase v)

type Prim = PrimitiveDatatype ()

tcError :: (MonadIO m,Location loc) => Position -> TypecheckerErr -> TcM loc m a
tcError pos msg = throwTcError $ TypecheckerError pos msg  

genTcError :: (MonadIO m,Location loc) => Position -> Doc -> TcM loc m a
genTcError pos msg = throwTcError $ TypecheckerError pos $ GenTcError msg  

throwTcError :: (MonadIO m,Location loc) => SecrecError -> TcM loc m a
throwTcError err = do
    (i,f) <- Reader.ask
    let err2 = f err
    ios <- liftM openedCstrs State.get
    let add io = liftIO $ writeUniqRef (kStatus io) (Erroneous err2)
    mapM_ add ios
    throwError err2     

removeOrWarn :: SecrecError -> SecrecError
removeOrWarn = everywhere (mkT f) where
    f (OrWarn err) = err
    f err = err

varIdxT :: VarName VarIdentifier Type -> Type
varIdxT v = IdxT $ varExpr v

askOpts :: Monad m => TcM loc m Options
askOpts = TcM $ lift ask

localOpts :: Monad m => (Options -> Options) -> TcM loc m a -> TcM loc m a
localOpts f (TcM m) = TcM $ RWS.mapRWST (SecrecM . Reader.local f . unSecrecM) m

withoutImplicitClassify :: Monad m => TcM loc m a -> TcM loc m a
withoutImplicitClassify m = localOpts (\opts -> opts { implicitClassify = False }) m

instance MonadIO m => GenVar VarIdentifier (TcM loc m) where
    genVar v = uniqVarId (varIdBase v) (varIdPretty v)

instance MonadIO m => GenVar VarIdentifier (SecrecM m) where
    genVar v = freshVarId (varIdBase v) (varIdPretty v)

instance (MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m VarIdentifier where
    traverseVars f n = do
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        return n
    substL v = return $ Just v

-- filter the constraints that depend on a set of variables
varsCstrGraph :: (VarsIdTcM loc m,Location loc) => Set VarIdentifier -> IOCstrGraph loc -> TcM loc m (IOCstrGraph loc)
varsCstrGraph vs gr = labnfilterM aux (Graph.trc gr)
    where
    aux (i,x) = do
        xvs <- liftM Map.keysSet $ fvs x
        if Set.null (vs `Set.intersection` xvs)
            then return False
            else return True

-- gets the terminal nodes in the constraint graph for all the variables in a given value
getVarOutSet :: (VarsIdTcM loc m,VarsId (TcM loc m) a,Location loc) => a -> TcM loc m (Set (Loc loc IOCstr))
getVarOutSet x = do
    -- get the free variables
    vs <- liftM Map.keysSet $ fvs x
    gr <- liftM (tCstrs . head . tDict) State.get
    gr' <- varsCstrGraph vs gr
    return $ Set.fromList $ map snd $ endsGr gr'

compoundStmt :: Location loc => [Statement iden (Typed loc)] -> Statement iden (Typed loc)
compoundStmt ss = CompoundStatement (Typed noloc t) ss
    where t = StmtType $ mconcat $ map ((\(StmtType c) -> c) . typed . loc) ss
    
moduleVarId :: Module VarIdentifier loc -> VarIdentifier
moduleVarId = maybe (mkVarId "main") id . moduleId    
    
    
    
