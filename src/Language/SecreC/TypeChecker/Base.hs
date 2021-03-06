{-# LANGUAGE CPP, TemplateHaskell, MagicHash, DeriveGeneric, Rank2Types, UndecidableInstances, DeriveFoldable, DeriveTraversable, FlexibleContexts, ConstraintKinds, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils as Utils
import Language.SecreC.Error
import Language.SecreC.Pretty as PP
import Language.SecreC.Vars
import Language.SecreC.Parser.PreProcessor

import Data.Foldable
import Data.UnixTime
import Data.IORef
import Data.Binary as Binary
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
import Data.Map (Map(..),(!))
import qualified Data.Map as Map
import Data.Bifunctor
import Data.Hashable
import Data.SBV (Symbolic)
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.Query as Graph hiding (mapFst,mapSnd)
import Data.Text.Unsafe

import GHC.Generics (Generic)
#if MIN_VERSION_base(4,9,0)
import GHC.Base hiding (mapM,Type)
#else
import GHC.Base hiding (mapM)
#endif
import GHC.Num

import Control.Applicative
import Control.Monad.State.Strict (State(..),StateT(..),MonadState(..))
import qualified Control.Monad.State.Strict as State
import Control.Monad.Reader (Reader(..),ReaderT(..),MonadReader(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.Writer.Strict (Writer(..),WriterT(..),MonadWriter(..))
import qualified Control.Monad.Writer.Strict as Writer hiding ((<>))
import Control.Monad.Trans.RWS.Strict (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Control.Monad.Except
import Control.Monad.Trans.Control
import Control.Monad.Identity
import Control.DeepSeq as DeepSeq

import Safe

import Unsafe.Coerce

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as PP

import System.IO.Unsafe
#if INCREMENTAL
import qualified System.Mem.Weak.Map as WeakMap
import System.Mem.Weak.Exts as Weak
import qualified Data.HashTable.Weak.IO as WeakHash
#endif
import System.Exit
import System.IO
import System.Posix.Types
import System.Posix.Files
import System.FilePath.Posix
import System.IO.Error

data SolveMode = SolveMode
    { solveFail :: SolveFail -- when to fail solving constraints
    , solveScope :: SolveScope -- which constraints to solve
    }
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

data SolveFail
    = FirstFail Bool -- fail on first non-halt error (receives halt failure as parameter)
    | AllFail Bool -- compile all errors (receives halt failure as parameter)
    | NoFail -- do not fail on error
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

haltFail :: SolveFail -> Bool
haltFail (FirstFail h) = h
haltFail (AllFail h) = h
haltFail NoFail = False

mkHaltFailMode :: SolveMode -> SolveMode
mkHaltFailMode m = m { solveFail = mkHaltFail (solveFail m) }

mkHaltFail :: SolveFail -> SolveFail
mkHaltFail (FirstFail _) = FirstFail True
mkHaltFail (AllFail _) = AllFail True
mkHaltFail NoFail = NoFail

data SolveScope
    = SolveAll -- solve all constraints
    | SolveGlobal -- solve all but delayable constraints
    | SolveLocal -- do not solve global constraints
  deriving (Data,Typeable,Show,Eq,Generic)

instance Ord SolveScope where
    compare SolveLocal SolveLocal = EQ
    compare SolveLocal _ = LT
    compare _ SolveLocal = GT
    compare SolveGlobal SolveGlobal = EQ
    compare SolveGlobal _ = LT
    compare _ SolveGlobal = GT
    compare SolveAll SolveAll = EQ

-- warn for unused local variables


#if INCREMENTAL
type GCstr = IOCstr
{-# INLINE gCstrId #-}
gCstrId = ioCstrId
data IOCstr = IOCstr
    { kCstr :: TCstr
    , kStatus :: (IdRef ModuleTyVarId TCstrStatus)
    }
  deriving (Data,Typeable,Show)
instance Hashable IOCstr where
    {-# INLINE hashWithSalt #-}
    hashWithSalt i k = hashWithSalt i (kCstr k)
instance Eq IOCstr where
    {-# INLINE (==) #-}
    k1 == k2 = kStatus k1 == kStatus k2
instance Ord IOCstr where
    {-# INLINE compare #-}
    compare k1 k2 = compare (kStatus k1) (kStatus k2)
instance (DebugM m) => PP m IOCstr where
    {-# INLINE pp #-}
    pp k = do
        pp1 <- pp (ioCstrId k)
        pp2 <- pp (kCstr k)
        returnS $ pp1 <+> char '=' <+> pp2
        
ioCstrId :: IOCstr -> Int
{-# INLINE ioCstrId #-}
ioCstrId = hashModuleTyVarId . uniqId . kStatus

ioCstrUnique :: IOCstr -> ModuleTyVarId
{-# INLINE ioCstrUnique #-}
ioCstrUnique = uniqId . kStatus
#else
type GCstr = IdCstr
{-# INLINE gCstrId #-}
gCstrId = hashModuleTyVarId . kId
data IdCstr = IdCstr
    { kCstr :: TCstr
    , kId :: ModuleTyVarId
    }
  deriving (Data,Typeable,Show)

instance Hashable IdCstr where
    {-# INLINE hashWithSalt #-}
    hashWithSalt i k = hashWithSalt i (kCstr k)
  
instance Eq IdCstr where
    {-# INLINE (==) #-}
    k1 == k2 = kId k1 == kId k2
instance Ord IdCstr where
    {-# INLINE compare #-}
    compare k1 k2 = compare (kId k1) (kId k2)

instance (DebugM m) => PP m IdCstr where
    {-# INLINE pp #-}
    pp k = do
        pp1 <- pp (kId k)
        pp2 <- pp (kCstr k)
        returnS $ pp1 <+> char '=' <+> pp2
#endif

#if INCREMENTAL
data TCstrStatus
    = Unevaluated -- has never been evaluated
    | Evaluated -- has been evaluated
        TDict -- resolved dictionary (variables bindings and recursive constraints)
        (Frees,Frees) -- (new frees,old frees)
        Bool -- is inferred
        ShowOrdDyn -- result value
    | Erroneous -- has failed
        SecrecError -- failure error
  deriving (Data,Typeable,Show,Generic,Eq,Ord)
instance Hashable TCstrStatus
#endif

data Scope = GlobalScope | LocalScope
  deriving (Show,Read,Data,Typeable,Generic)

instance Binary Scope
instance Hashable Scope

instance Monad m => PP m Scope where
    pp GlobalScope = returnS $ text "global"
    pp LocalScope = returnS $ text "local"

#if INCREMENTAL
{-# NOINLINE globalEnv #-}
globalEnv :: IORef GlobalEnv
globalEnv = unsafePerformIO (newGlobalEnv >>= newIORef)

newGlobalEnv :: IO GlobalEnv
newGlobalEnv = do
    m <- WeakHash.newSized (1024*4)
    iom <- WeakHash.newSized (1024*4)
    cstrs <- WeakHash.newSized 2048
    returnS $ GlobalEnv m iom cstrs

backupGlobalEnv :: IO GlobalEnv
backupGlobalEnv = do
    g <- readIORef globalEnv
    freshGlobalEnv
    returnS g
    
restoreGlobalEnv :: GlobalEnv -> IO ()
restoreGlobalEnv g = do
    resetGlobalEnv False
    writeIORef globalEnv g

resetGlobalEnv :: Bool -> IO ()
resetGlobalEnv doFresh = do
    g <- readIORef globalEnv
    WeakHash.finalize $ tDeps g
    WeakHash.finalize $ ioDeps g
    WeakHash.finalize $ gCstrs g
    when doFresh $ freshGlobalEnv

freshGlobalEnv :: IO ()
freshGlobalEnv = do
    deps <- WeakHash.newSized 1024
    iodeps <- WeakHash.newSized 512
    cstrs <- WeakHash.newSized 2048
    writeIORef globalEnv $ GlobalEnv { tDeps = deps, ioDeps = iodeps, gCstrs = cstrs }
#endif

orWarn :: (MonadIO m) => TcM m a -> TcM m (Maybe a)
orWarn m = (liftM Just m) `catchError` \e -> do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Map.singleton (loc e) $ Set.singleton $ ErrWarn e
--    liftIO $ putStrLn $ "warning... " ++ ppr e
    returnS Nothing

orWarn_ :: (MonadIO m) => TcM m a -> TcM m ()
orWarn_ m = orWarn m >> returnS ()

type POId = GIdentifier --Either VarIdentifier (Op GIdentifier ())

type GIdentifier = GIdentifier' ()

data GIdentifier' t
    = VIden VarIdentifier -- variable
    | PIden VarIdentifier -- function or procedure or lemma
    | OIden (Op GIdentifier t) -- operator function or procedure
    | TIden VarIdentifier -- type
    | MIden VarIdentifier -- module
  deriving (Eq,Ord,Show,Data,Typeable,Generic,Functor)
instance Hashable t => Hashable (GIdentifier' t)
instance Binary t => Binary (GIdentifier' t)

instance (DebugM m) => PP m (GIdentifier' t) where
    pp (VIden v) = pp v
    pp (PIden v) = pp v
    pp (OIden v) = pp v
    pp (TIden v) = pp v
    pp (MIden v) = pp v

unVIden :: GIdentifier -> VarIdentifier
unVIden = unVIden'

unVIden' :: GIdentifier' t -> VarIdentifier
unVIden' (VIden v) = v

isVIden :: GIdentifier -> Bool
isVIden = isVIden

isVIden' :: GIdentifier' t -> Bool
isVIden' (VIden _) = True
isVIden' _ = False

isOIden :: GIdentifier -> Bool
isOIden = isOIden'

isOIden' :: GIdentifier' t -> Bool
isOIden' (OIden _) = True
isOIden' _ = False

videns :: Set GIdentifier -> Set VarIdentifier
videns = videns'

videns' :: Set (GIdentifier' t) -> Set VarIdentifier
videns' gs = Set.foldr aux Set.empty gs
    where
    aux (VIden v) vs = Set.insert v vs
    aux _ vs = vs

gIdenBase :: (DebugM m) => GIdentifier -> m String
gIdenBase = gIdenBase'

gIdenBase' :: (DebugM m) => GIdentifier' t -> m String
gIdenBase' (VIden v) = returnS $ varIdBase v
gIdenBase' (PIden v) = returnS $ varIdBase v
gIdenBase' (TIden v) = returnS $ varIdBase v
gIdenBase' (MIden v) = returnS $ varIdBase v
gIdenBase' (OIden o) = ppr o

#if INCREMENTAL
data GlobalEnv = GlobalEnv
    { tDeps :: WeakHash.BasicHashTable GIdentifier (WeakMap.WeakMap TyVarId IOCstr) -- IOCstr dependencies on variables
    , ioDeps :: WeakHash.BasicHashTable TyVarId (WeakMap.WeakMap TyVarId IOCstr) -- IOCstr dependencies on other IOCstrs
    , gCstrs :: WeakHash.BasicHashTable TCstr IOCstr -- hashtable of generated constraints for possbile reuse
    }
-- solved constraints whose solutions have been delayed
type CstrCache = Map LocGCstr TCstrStatus
#else
type CstrSols = Map LocGCstr ShowOrdDyn
#endif

-- dependency tracking
type Deps = Set LocGCstr

getModuleCount :: (Monad m) => TcM m Int
getModuleCount = liftM (snd . moduleCount) State.get

type ModuleCount = (Maybe ((String,TyVarId),Int),Int)

-- global typechecking environment
data TcEnv = TcEnv {
      localVars  :: Map GIdentifier (Bool,Bool,EntryEnv) -- ^ local variables: name |-> (isConst,isAnn,type of the variable)
    , localFrees :: Frees -- ^ free internal const variables generated during typechecking
    , localConsts :: Map Identifier GIdentifier
    , globalDeps :: Deps -- ^ global dependencies
    , localDeps :: Deps -- ^ local dependencies
    , tDict :: NeList TDict -- ^ A stack of dictionaries
    , openedCstrs :: [(GCstr,Set VarIdentifier)] -- constraints being resolved, for dependency tracking: ordered map from constraints to bound variables
#if INCREMENTAL
    , cstrCache :: CstrCache -- cache for constraints
    , solveToCache :: Bool -- solve constraints to the cache or global state
#else
    , recordSols :: Bool -- when to record constraint solutions
    , cstrSols :: CstrSols -- constraint solutions (for hypotheses)
#endif
    , lineage :: Lineage -- lineage of the constraint being processed
    , moduleCount :: ModuleCount
    , inTemplate :: Maybe ([TemplateTok],Bool) -- if typechecking inside a template, global constraints are delayed (templates tokens, with context flag)
    , decKind :: DecKind -- if typechecking inside a declaration
    , exprC :: ExprClass -- type of expression
    , isLeak :: Bool -- if typechecking leakage expressions
    , isDef :: Bool -- if typechecking variable initializations
    , decClass :: DecClass -- class when typechecking procedures
    , moduleEnv :: (ModuleTcEnv,ModuleTcEnv) -- (aggregate module environment for past modules,plus the module environment for the current module)
    , progressBar :: (String,Int) -- message, current line
    }

type TemplateTok = Var

data DecKind
    = AKind -- axiom
    | LKind -- lemma
    | PKind -- procedure
    | FKind -- function
    | TKind -- axiom
  deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Hashable DecKind
instance Binary DecKind

instance Monad m => PP m DecKind where
    pp = returnS . text . show

--type LazyEntryEnv = Either EntryEnv (ModuleCount,GlobalDeclaration Identifier Position)

-- module typechecking environment that can be exported to an interface file
data ModuleTcEnv = ModuleTcEnv {
      globalVars :: Map GIdentifier (Maybe Expr,(Bool,Bool,EntryEnv)) -- ^ global variables: name |-> (isConst,isAnn,type of the variable)
    , globalConsts :: Map Identifier GIdentifier -- mapping from declared const variables to unique internal const variables: consts have to be in SSA to guarantee the typechecker's correctness
    , kinds :: Map GIdentifier EntryEnv -- ^ defined kinds: name |-> type of the kind
    , domains :: Map GIdentifier EntryEnv -- ^ defined domains: name |-> type of the domain
    -- a list of overloaded procedures; akin to Haskell type class operations
    -- we don't allow specialization of function templates
    , procedures :: Map POId (Map ModuleTyVarId EntryEnv) -- ^ defined procedures: name |-> procedure decl
    -- | a base template and a list of specializations; akin to Haskell type functions
    , functions :: Map POId (Map ModuleTyVarId EntryEnv)
    , lemmas :: Map GIdentifier (Map ModuleTyVarId EntryEnv)
    , structs :: Map GIdentifier (Map ModuleTyVarId EntryEnv) -- ^ defined structs: name |-> struct decl
    , axioms :: Map ModuleTyVarId EntryEnv -- defined axioms
    } deriving (Generic,Data,Typeable,Eq,Ord,Show)

instance Hashable ModuleTcEnv

instance Monad m => PP m ModuleTcEnv where
    pp = returnS . text . show

instance Binary (ModuleTcEnv)

instance Monoid (ModuleTcEnv) where
    mempty = ModuleTcEnv {
          globalVars = Map.empty
        , globalConsts = Map.empty
        , kinds = Map.empty
        , domains = Map.empty
        , procedures = Map.empty
        , functions = Map.empty
        , lemmas = Map.empty
        , axioms = Map.empty
        , structs = Map.empty
        }
    mappend x y = ModuleTcEnv {
          globalVars = Map.union (globalVars x) (globalVars y)
        , globalConsts = Map.union (globalConsts x) (globalConsts y)
        , kinds = Map.union (kinds x) (kinds y)
        , domains = Map.union (domains x) (domains y)
        , procedures = Map.unionWith Map.union (procedures x) (procedures y)
        , functions = Map.unionWith Map.union (functions x) (functions y)
        , lemmas = Map.unionWith Map.union (lemmas x) (lemmas y)
        , axioms = Map.union (axioms x) (axioms y)
        , structs = Map.unionWith Map.union (structs x) (structs y)
        }

--unionLazyEntryEnv :: LazyEntryEnv -> LazyEntryEnv -> LazyEntryEnv
--unionLazyEntryEnv (Left e1) _ = Left e1
--unionLazyEntryEnv _ (Left e2) = Left e2
--unionLazyEntryEnv l r = r

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m ModuleTcEnv where
    traverseVars f (ModuleTcEnv x1 x2 x3 x4 x5 x6 x7 x8 x9) = do
        x1' <- f x1
        x2' <- traverseMap returnS f x2
        x3' <- f x3
        x4' <- f x4
        x5' <- f x5
        x6' <- f x6
        x7' <- f x7
        x8' <- f x8
        x9' <- f x9
        returnS $ ModuleTcEnv x1' x2' x3' x4' x5' x6' x7' x8' x9'

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m EntryEnv where
    traverseVars f (EntryEnv x1 x2) = do
        x1' <- f x1
        x2' <- f x2
        returnS $ EntryEnv x1' x2'

--mergeStructs (x,y) (z,w) = (unionMb x z,Map.union y w)
unionMb Nothing y = y
unionMb x Nothing = x
unionMb (Just x) (Just y) = error "unionMb: cannot join two justs"

withExprC :: Monad m => ExprClass -> TcM m a -> TcM m a
withExprC b m = do
    old <- liftM exprC State.get
    State.modify $ \env -> env { exprC = b }
    x <- m
    State.modify $ \env -> env { exprC = old }
    returnS x

limitExprC :: Monad m => ExprClass -> TcM m a -> TcM m a
limitExprC c' m = do
    c <- getExprC
    withExprC (min c c') m

withLeak :: Monad m => Bool -> TcM m a -> TcM m a
withLeak b m = do
    old <- liftM isLeak State.get
    State.modify $ \env -> env { isLeak = b }
    x <- m
    State.modify $ \env -> env { isLeak = old }
    returnS x

#if INCREMENTAL
runOnCache :: MonadIO m => TcM m a -> TcM m a
runOnCache m = do
   (x,cache) <- onCache m
   forM_ (Map.toList cache) $ \(Loc p iok,st) ->  writeCstrStatus p iok st
   returnS x
    
onCache :: Monad m => TcM m a -> TcM m (a,CstrCache)
onCache m = do
    oldcache <- State.gets cstrCache
    oldsolve <- State.gets solveToCache
    State.modify $ \env -> env { cstrCache = Map.empty, solveToCache = True }
    x <- m
    cache <- State.gets cstrCache
    State.modify $ \env -> env { solveToCache = oldsolve, cstrCache = oldcache }
    returnS (x,cache)
#else
runOnCache :: MonadIO m => TcM m a -> TcM m a
runOnCache m = m

onCache :: Monad m => TcM m a -> TcM m (a,())
onCache m = liftM (,()) m
#endif

withKind :: Monad m => DecKind -> TcM m a -> TcM m a
withKind k m = do
    old <- liftM decKind State.get
    State.modify $ \env -> env { decKind = k }
    x <- m
    State.modify $ \env -> env { decKind = old }
    returnS x

getExprC :: Monad m => TcM m ExprClass
getExprC = liftM exprC State.get
    
getLeak :: Monad m => TcM m Bool
getLeak = liftM isLeak State.get

getLineage :: Monad m => TcM m Lineage
getLineage = State.gets lineage

getKind :: Monad m => TcM m (DecKind)
getKind = State.gets decKind

getDef :: Monad m => TcM m (Bool)
getDef = State.gets isDef

getInCtx :: Monad m => TcM m Bool
getInCtx = State.gets (maybe True snd . inTemplate)

getCstrState :: Monad m => TcM m CstrState
getCstrState = do
    isAnn <- getAnn
    isDef <- getDef
    exprC <- getExprC
    lineage <- getLineage
    isLeak <- getLeak
    kind <- getKind
    err <- Reader.ask
    returnS $ CstrState isAnn isDef exprC isLeak kind lineage err
    
getAnn :: Monad m => TcM m Bool
getAnn = liftM (isAnnDecClass . decClass) State.get

modifyModuleEnv :: Monad m => (ModuleTcEnv -> ModuleTcEnv) -> TcM m ()
modifyModuleEnv f = State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,f y) }

modifyModuleEnvM :: Monad m => (ModuleTcEnv -> TcM m ModuleTcEnv) -> TcM m ()
modifyModuleEnvM f = do
    y <- State.gets (snd . moduleEnv)
    y' <- f y
    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y') }

remDecDict :: DecType -> DecType
remDecDict d@(DecType i isRec ts hctx bctx specs b) =
    DecType i isRec ts hctx{dCtxDict = emptyPureTDict} bctx{dCtxDict = emptyPureTDict} specs b

isInlineDec :: DecType -> Bool
isInlineDec = isInlineDecClass . decDecClass

decDecClass :: DecType -> DecClass
decDecClass (DecType _ _ _ _ _ _ b) = iDecDecClass b

iDecDecClass :: InnerDecType -> DecClass
iDecDecClass d@(ProcType pl n pargs pret panns body cl) = cl
iDecDecClass d@(FunType isLeak pl n pargs pret panns body cl) = cl
iDecDecClass d@(StructType sl sid atts cl) = cl
iDecDecClass d@(AxiomType isLeak p qs pargs cl) = cl
iDecDecClass d@(LemmaType isLeak pl n pargs panns body cl) = cl

hasDecBody :: DecType -> Bool
hasDecBody d@(DecType i isRec ts hctx bctx specs b) = hasIDecBody b

hasIDecBody :: InnerDecType -> Bool
hasIDecBody d@(ProcType pl n pargs pret panns body cl) = isJust body
hasIDecBody d@(FunType isLeak pl n pargs pret panns body cl) = isJust body
hasIDecBody d@(StructType sl sid atts cl) = isJust atts
hasIDecBody d@(AxiomType isLeak p qs pargs cl) = True
hasIDecBody d@(LemmaType isLeak pl n pargs panns body cl) = isJust body

remDecBody :: DecType -> DecType
remDecBody d@(DecType i isRec ts hctx bctx specs b) =
    DecType i isRec ts hctx bctx specs (remIDecBody b)

remIDecBody :: InnerDecType -> InnerDecType
remIDecBody d@(ProcType pl n pargs pret panns body cl) = ProcType pl n pargs pret panns Nothing cl
remIDecBody d@(FunType isLeak pl n pargs pret panns body cl) = FunType isLeak pl n pargs pret panns Nothing cl
remIDecBody d@(StructType sl sid atts cl) = StructType sl sid Nothing cl
remIDecBody d@(AxiomType isLeak p qs pargs cl) = AxiomType isLeak p qs pargs cl
remIDecBody d@(LemmaType isLeak pl n pargs panns body cl) = LemmaType isLeak pl n pargs panns Nothing cl

filterAnns :: Bool -> Bool -> (DecTypeK -> Bool) -> Map x (Map y EntryEnv) -> Map x (Map y EntryEnv)
filterAnns isAnn isLeak decK = Map.map (filterAnns1 isAnn isLeak decK)

filterAnns1 :: Bool -> Bool -> (DecTypeK -> Bool) -> (Map y EntryEnv) -> (Map y EntryEnv)
filterAnns1 isAnn isLeak decK = Map.filter p
    where
    p e@(entryType -> t@(DecT d)) =
        (isAnn >= isAnnDecClass (tyDecClass t))
        && (isLeak >= isLeakDec d)
        && (decK $ decTypeKind d)

insideAnnotation :: Monad m => TcM m a -> TcM m a
insideAnnotation = withAnn True

withAnn :: Monad m => Bool -> TcM m a -> TcM m a
withAnn b m = do
    isAnn <- liftM (isAnnDecClass . decClass) State.get
    State.modify $ \env -> env { decClass = chgAnnDecClass b (decClass env) }
    x <- m
    State.modify $ \env -> env { decClass = chgAnnDecClass isAnn (decClass env) }
    returnS x

withDef :: Monad m => Bool -> TcM m a -> TcM m a
withDef b m = do
    o <- liftM isDef State.get
    State.modify $ \env -> env { isDef = b }
    x <- m
    State.modify $ \env -> env { isDef = o }
    returnS x

chgAnnDecClass :: Bool -> DecClass -> DecClass
chgAnnDecClass b (DecClass _ i r w) = DecClass b i r w

chgInlineDecClass :: Bool -> DecClass -> DecClass
chgInlineDecClass b (DecClass a _ r w) = DecClass a b r w

isAnnDecClass :: DecClass -> Bool
isAnnDecClass (DecClass b _ _ _) = b

isInlineDecClass :: DecClass -> Bool
isInlineDecClass (DecClass _ b _ _) = b

withDependencies :: Monad m => Set LocGCstr -> TcM m a -> TcM m a
withDependencies deps m = do
    State.modify $ \env -> env { localDeps = deps `Set.union` localDeps env }
    x <- m
    State.modify $ \env -> env { localDeps = localDeps env }
    returnS x

type VarsG m a = Vars GIdentifier m a
type VarsGTcM m = (Typeable m,MonadIO m,MonadBaseControl IO m,VarsG (TcM m) Position,VarsG (TcM Symbolic) Position)

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv
    { 
    localVars = Map.empty
    , localFrees = Map.empty
    , globalDeps = Set.empty
    , localDeps = Set.empty
    , tDict = WrapNe emptyTDict
    , openedCstrs = []
#if INCREMENTAL
    , cstrCache = Map.empty
    , solveToCache = False
#else
    , cstrSols = Map.empty
    , recordSols = False
#endif
    , lineage = []
    , moduleCount = (Nothing,0)
    , inTemplate = Nothing
    , decKind = FKind
    , exprC = ReadOnlyExpr
    , isLeak = False
    , localConsts = Map.empty
    , decClass = DecClass False False emptyDecClassVars emptyDecClassVars
    , moduleEnv = (mempty,mempty)
    , isDef = False
    , progressBar = ("",0)
    }

data EntryEnv = EntryEnv {
      entryLoc :: Position -- ^ Location where the entry is defined
    , entryType :: Type -- ^ Type of the entry
    }
  deriving (Generic,Data,Typeable,Eq,Ord,Show)

instance Binary EntryEnv  

instance Located EntryEnv where
    type LocOf EntryEnv = Position
    loc = entryLoc
    updLoc e l = e { entryLoc = l }
   
instance (DebugM m) => PP m EntryEnv where
    pp = pp . entryType
   
varNameToType :: Var -> Type
varNameToType (VarName (KType b) (VIden k)) = KindT $ KVar k b
varNameToType (VarName (KindT k) (VIden n)) = SecT $ SVar n k
varNameToType (VarName (TType b) (VIden n)) = ComplexT $ CVar n b
varNameToType (VarName (BType c) (VIden n)) = BaseT $ BVar n c
varNameToType (VarName DType (VIden n)) = DecT $ DVar n
varNameToType (VarName (VAType b sz) (VIden n)) = VArrayT $ VAVar n b sz
varNameToType (VarName t n) | typeClass "varNameToType" t == TypeC = IdxT (RVariablePExpr t $ VarName t n)
varNameToType v = error $ "varNameToType " ++ show v

--condVarNameToType :: Constrained Var -> Type
--condVarNameToType (Constrained v c) = constrainedType (varNameToType v) c

typeToVarName :: Type -> Maybe Var
typeToVarName (KindT (KVar n b)) = Just $ VarName (KType b) $ VIden n
typeToVarName (SecT (SVar n k)) = Just (VarName (KindT k) $ VIden n)
typeToVarName (ComplexT (CVar n b)) = Just (VarName (TType b) $ VIden n)
typeToVarName (BaseT (BVar n c)) = Just (VarName (BType c) $ VIden n)
typeToVarName (DecT (DVar n)) = Just (VarName DType $ VIden n)
typeToVarName (VArrayT (VAVar n b sz)) = Just (VarName (VAType b sz) $ VIden n)
typeToVarName (IdxT (RVariablePExpr _ (VarName t n))) | typeClass "typeToVarName" t == TypeC = Just (VarName t n)
typeToVarName _ = Nothing

tyToVar :: Type -> Var
tyToVar = fromJustNote "tyToVar" . typeToVarName

typeToTypeName :: Type -> Maybe (TypeName GIdentifier Type)
typeToTypeName t = case typeToVarName t of
    Just (VarName _ n) -> Just $ TypeName t n
    otherwise -> Nothing
    
typeToDomainName :: Type -> Maybe (DomainName GIdentifier Type)
typeToDomainName t = case typeToVarName t of
    Just (VarName _ n) -> Just $ DomainName t n
    otherwise -> Nothing

typeToKindName :: Type -> Maybe (KindName GIdentifier Type)
typeToKindName t = case typeToVarName t of
    Just (VarName _ n) -> Just $ KindName t n
    otherwise -> Nothing

newtype SecrecErrArr = SecrecErrArr { unSecrecErrArr :: SecrecError -> SecrecError }
    deriving (Generic,Data,Typeable,Show)

instance Binary SecrecErrArr where
    put (SecrecErrArr f) = Binary.put (f ErrToken)
    get = do
        err <- Binary.get
        let aux :: SecrecError -> SecrecError -> SecrecError
            aux x ErrToken = x
            aux x e = e
        returnS $ SecrecErrArr $ \x -> everywhere (mkT $ aux x) err
instance Hashable SecrecErrArr where
    hashWithSalt salt err = salt

liftTcM :: Monad m => SecrecM m a -> TcM m a
liftTcM m = TcM $ lift m

newtype TcM m a = TcM { unTcM :: RWST (Int,SecrecErrArr) () (TcEnv) (SecrecM m) a }
    deriving (Functor,Applicative,Typeable,Monad,MonadIO,MonadState (TcEnv),MonadReader (Int,SecrecErrArr),MonadWriter (),Alternative)
    
instance MonadIO m => MonadPlus (TcM m) where
    {-# INLINE mzero #-}
    mzero = TcM mzero
    {-# INLINE mplus #-}
    mplus x y = catchError x (const y)
    
instance MonadIO m => MonadError SecrecError (TcM m) where
    {-# INLINE throwError #-}
    throwError e = TcM $ throwError e
    {-# INLINE catchError #-}
    catchError m f = TcM $ catchError (unTcM $ runOnCache m) (unTcM . f)

localOptsTcM :: Monad m => (Options -> Options) -> TcM m a -> TcM m a
localOptsTcM f (TcM m) = TcM $ RWS.mapRWST (Reader.local f) m

mapTcM :: (m (Either SecrecError ((a,TcEnv,()),SecrecWarnings)) -> n (Either SecrecError ((b,TcEnv,()),SecrecWarnings)))
    -> TcM m a -> TcM n b
mapTcM f (TcM m) = TcM $ RWS.mapRWST (mapSecrecM f) m

flushTcWarnings :: MonadIO m => TcM m a -> TcM m a
flushTcWarnings = mapTcM flush
    where
    flush m = do
        e <- m
        case e of
            Left err -> returnS $ Left $ DeepSeq.force $ err
            Right ((x,env,()),warns) -> do
                liftIO $ printWarns $ warns
                liftIO $ hFlush stdout
                liftIO $ hFlush stderr
                x `seq` env `seq` returnS (Right ((x,env,()),mempty))

instance MonadTrans (TcM) where
    lift m = TcM $ lift $ SecrecM $ lift $ liftM (\x -> Right (x,mempty)) m

askErrorM :: Monad m => TcM m (SecrecError -> SecrecError)
askErrorM = liftM (unSecrecErrArr . snd) $ Reader.ask

askErrorM' :: Monad m => TcM m (Int,SecrecError -> SecrecError)
askErrorM' = do
    (i,SecrecErrArr f) <- Reader.ask
    returnS (i,f)
    
askErrorM'' :: Monad m => TcM m (Int,SecrecErrArr)
askErrorM'' = Reader.ask

newErrorM :: TcM m a -> TcM m a
newErrorM (TcM m) = TcM $ RWS.withRWST (\f s -> ((0,SecrecErrArr id),s)) m

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: (Monad m,Location loc) => loc -> TcM m a -> TcM m a
tcBlock l m = do
    r <- Reader.ask
    s <- State.get
    (x,s',w') <- TcM $ lift $ runRWST (unTcM m) r s
    Writer.tell w'
    returnS x
    
tcDictBlock :: Monad m => TcM m a -> TcM m a
tcDictBlock m = do
    dicts <- State.gets tDict
    x <- m
    State.modify $ \env -> env { tDict = dicts }
    returnS x

execTcM :: (MonadIO m) => TcM m a -> (Int,SecrecErrArr) -> TcEnv -> SecrecM m (a,TcEnv)
execTcM m arr env = do
    (x,env',()) <- RWS.runRWST (unTcM m) arr env
    returnS (x,env')

runTcM :: (MonadIO m) => TcM m a -> SecrecM m a
runTcM m = liftM fst $ RWS.evalRWST (unTcM m') (0,SecrecErrArr id) emptyTcEnv
    where
    m' = do
        -- add default coercion declaration
        dec <- coercesDec
        let Just (g,tid) = decTypeId dec
        modifyModuleEnv $ \env -> env { functions = Map.insert g (Map.singleton tid $ EntryEnv noloc $ DecT dec) $ functions env }
        -- run computation
        State.modify $ \env -> env { moduleCount = mapSnd succ (moduleCount env) }
        m

coercesDec :: MonadIO m => TcM m DecType
coercesDec = do
    i <- newModuleTyVarId
    let k1 = KVar ((mkVarId "K1") { varIdRead = True, varIdWrite = True }) Nothing
    let k2 = KVar ((mkVarId "K2") { varIdRead = True, varIdWrite = True }) Nothing
    let d1 = SVar ((mkVarId "D1") { varIdRead = True, varIdWrite = True }) k1
    let d2 = SVar ((mkVarId "D2") { varIdRead = True, varIdWrite = True }) k2
    let t1 = BVar ((mkVarId "T1") { varIdRead = True, varIdWrite = True }) Nothing
    let t2 = BVar ((mkVarId "T1") { varIdRead = True, varIdWrite = True }) Nothing
    let n1 = varExpr $ VarName (BaseT index) $ VIden $ (mkVarId "N1") { varIdRead = True, varIdWrite = True }
    let n2 = varExpr $ VarName (BaseT index) $ VIden $ (mkVarId "N2") { varIdRead = True, varIdWrite = True }
    let ts = [(Constrained (tyToVar $ KindT k1) Nothing,False),(Constrained (tyToVar $ KindT k2) Nothing,False),(Constrained (tyToVar $ SecT d1) Nothing,False),(Constrained (tyToVar $ SecT d2) Nothing,False),(Constrained (tyToVar $ BaseT t1) Nothing,False),(Constrained (tyToVar $ BaseT t2) Nothing,False),(Constrained (tyToVar $ IdxT n1) Nothing,False),(Constrained (tyToVar $ IdxT n2) Nothing,False)]
    let e = VarName (ComplexT $ CType d1 t1 n1) $ VIden $ (mkVarId "e") { varIdWrite = False }
    let ret = ComplexT $ CType d2 t2 n2
    let x = VarName ret $ VIden $ mkVarId "cx"
    st <- getCstrState
    let kst = CstrState False False PureExpr False FKind (cstrLineage st) (cstrErr st)
    let k = TcK (Coerces Nothing (varExpr e) x) kst
    let g = Graph.mkGraph [(0,Loc noloc k)] []
    let ctx = DecCtx Nothing (PureTDict g emptyTSubsts mempty) (Map.singleton (mkVarId "cx") False)
    let dec = DecType i (DecTypeOri False) ts implicitDecCtx ctx [] $ FunType False noloc (OIden $ OpCoerce noloc) [(False,e,False)] ret [] (Just $ fmap (Typed noloc) $ varExpr x) (DecClass False True emptyDecClassVars emptyDecClassVars)
    debugTc $ do
        ppd <- ppr dec
        liftIO $ putStrLn $ "added base coercion dec " ++ ppd
    returnS dec

checkNoSecM :: Monad m => TcM m Bool
checkNoSecM = do
    cl <- State.gets decClass
    opts <- askOpts
    if isAnnDecClass cl
        then returnS True
        else returnS False

checkCoercionM :: Monad m => TcM m Bool
checkCoercionM = do
    opts <- askOpts
    st <- getCstrState
    noSec <- checkNoSecM
    returnS $ checkCoercion noSec (implicitCoercions opts) st
  where
    checkCoercion :: Bool -> CoercionOpt -> CstrState -> Bool
    checkCoercion True ((< ExtendedC) -> True) st = False
    checkCoercion noSec c st@(cstrDecK -> AKind) = False
    checkCoercion noSec OffC st = False
    checkCoercion noSec DefaultsC st = cstrIsDef st
    checkCoercion noSec OnC st = not $ cstrIsAnn st
    checkCoercion noSec ExtendedC st = True

-- flips errors whenever typechecking is expected to fail
failTcM :: (MonadIO m,Location loc) => loc -> TcM m a -> TcM m a
failTcM l m = do
    opts <- TcM $ lift Reader.ask
    if failTypechecker opts
        then catchError
            (m >> liftIO (die $ pprid $ GenericError (locpos l) (text "Typechecking should have failed") Nothing))
            (\e -> do
                ppe <- ppr e
                liftIO (hPutStrLn stderr ppe >> exitSuccess)
            )
        else m

type PIdentifier = GIdentifier' Type --Either VarIdentifier (Op GIdentifier Type)

-- | A template constraint with a result type
data TcCstr
    = TDec -- ^ type template declaration
        Bool -- check only context
        (Maybe [EntryEnv]) -- optional ambiguous entries
        SIdentifier -- template name
        [(Type,IsVariadic)] -- template arguments
        DecType -- resulting type
    | PDec -- ^ procedure declaration
        Bool -- check only context
        (Maybe [EntryEnv]) -- optional ambiguous entries
        PIdentifier -- procedure name
        (Maybe [(Type,IsVariadic)]) -- template arguments
        [(IsConst,Either Expr Type,IsVariadic)] -- procedure arguments
        Type -- returnS type
        DecType -- result
    | Equals
        Type Type -- ^ types equal
    | Coerces -- ^ types coercible
        (Maybe [Type]) -- optional bound variables, to delay the coercions' evaluation until these are unbound
        Expr
        Var
--    | CoercesN -- ^ multidirectional coercion
--        [(Expr,Var)]
    | CoercesLit -- coerce a literal expression into a specific type
        Expr -- literal expression with the base type given at the top-level
    | Unifies -- unification
        Type
        Type -- ^ type unification
    | Assigns -- assignment
        Type
        Type
    | SupportedPrint
        [(IsConst,Either Expr Type,IsVariadic)] -- ^ can call tostring on the argument type
        [Var] -- resulting coerced procedure arguments
    | ProjectStruct -- ^ struct type projection
        BaseType (AttributeName GIdentifier ()) 
        Type -- result
    | ProjectMatrix -- ^ matrix type projection
        Type
        [ArrayProj]
        Type -- result
    | IsReturnStmt
        (Set StmtClass) -- ^ is returnS statement
--    | MultipleSubstitutions
--        (Maybe Bool) -- optional testKO
--        [Type] -- bound variable
--        [([TCstr],[TCstr],Set VarIdentifier)] -- mapping from multiple matching conditions to their dependencies and free variables
    | MatchTypeDimension
        Expr -- type dimension
        [(Expr,IsVariadic)] -- sequence of sizes
    | IsValid -- check if an index condition is valid (this is mandatory: raises an error)
        Cond -- condition
    | NotEqual -- expressions not equal
        Expr
        Expr
    | TypeBase
        Type
        Type
    | IsPublic
        Bool
        Type
    | IsPrivate
        Bool
        Type
    | ToMultiset
        Type
        BaseType
    | ToSet
        (Either Type Type)
        BaseType -- left=base type, right=collection type
    | Resolve
        Type
    | Default
        (Maybe [(Expr,IsVariadic)])
        Expr
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

instance Binary TcCstr
instance Hashable TcCstr
 
isTrivialTcCstr :: TcCstr -> Bool
isTrivialTcCstr (Equals t1 t2) = t1 == t2
isTrivialTcCstr (Coerces _ e v) = e == varExpr v
isTrivialTcCstr (Unifies t1 t2) = t1 == t2
isTrivialTcCstr (Assigns t1 t2) = t1 == t2
isTrivialTcCstr (IsValid c) = c == trueExpr
isTrivialTcCstr _ = False
 
-- | checks (raise warnings)
data CheckCstr
    = CheckAssertion
        Cond -- condition
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

instance Binary CheckCstr
instance Hashable CheckCstr
 
isTrivialCheckCstr :: CheckCstr -> Bool
isTrivialCheckCstr (CheckAssertion c) = c == trueExpr
 
-- hypothesis (raises warnings)
data HypCstr
    = HypCondition -- c == True
        Expr
    | HypNotCondition -- c == False
        Expr
    | HypEqual -- e1 == e2
        Expr
        Expr
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

instance Binary HypCstr
instance Hashable HypCstr
 
isTrivialHypCstr :: HypCstr -> Bool
isTrivialHypCstr (HypCondition c) = c == trueExpr
isTrivialHypCstr (HypNotCondition c) = c == falseExpr
isTrivialHypCstr (HypEqual e1 e2) = e1 == e2
 
isTcCstr :: TCstr -> Bool
isTcCstr (TcK {}) = True
isTcCstr (CheckK {}) = False
isTcCstr (HypK {}) = False

isCheckCstr :: TCstr -> Bool
isCheckCstr (CheckK {}) = True
isCheckCstr (HypK {}) = False
isCheckCstr (TcK {}) = False

isHypCstr :: TCstr -> Bool
isHypCstr (HypK {}) = True
isHypCstr _ = False

isTrivialCstr :: TCstr -> Bool
isTrivialCstr (TcK c _) = isTrivialTcCstr c
isTrivialCstr (CheckK c _) = isTrivialCheckCstr c
isTrivialCstr (HypK c _) = isTrivialHypCstr c

type Var = VarName GIdentifier Type
type Expr = Expression GIdentifier Type
type ExprL loc = Expression GIdentifier (Typed loc)

type Lineage = [(GIdentifier,ModuleTyVarId)] -- trace of parent declarations

updCstrState :: (CstrState -> CstrState) -> TCstr -> TCstr
updCstrState f (TcK c st) = TcK c (f st)
updCstrState f (CheckK c st) = CheckK c (f st)
updCstrState f (HypK c st) = HypK c (f st)

data CstrState = CstrState
    { cstrIsAnn :: Bool
    , cstrIsDef :: Bool
    , cstrExprC :: ExprClass
    , cstrIsLeak :: Bool
    , cstrDecK :: DecKind
    , cstrLineage :: Lineage
    , cstrErr :: (Int,SecrecErrArr)
    }
  deriving (Data,Typeable,Show,Generic)
instance Binary CstrState
instance Hashable CstrState where
    hashWithSalt i (CstrState isAnn isDef expr isLeak dec line err) = i `hashWithSalt` isAnn `hashWithSalt` isDef `hashWithSalt` expr `hashWithSalt` isLeak `hashWithSalt` dec `hashWithSalt` line `hashWithSalt` err

noCstrSt :: CstrState
noCstrSt = CstrState False False ReadOnlyExpr False PKind [] (0,SecrecErrArr id)

data TCstr
    = TcK
        TcCstr -- constraint
        CstrState
    | CheckK
        CheckCstr
        CstrState
    | HypK
        HypCstr
        CstrState
  deriving (Data,Typeable,Show,Generic)

instance Binary TCstr
instance Hashable TCstr where
    hashWithSalt i (TcK c _) = i `hashWithSalt` (0::Int) `hashWithSalt` c
    hashWithSalt i (CheckK c _) = i `hashWithSalt` (1::Int) `hashWithSalt` c
    hashWithSalt i (HypK c _) = i `hashWithSalt` (2::Int) `hashWithSalt` c
 
instance Hashable EntryEnv
 
instance Eq TCstr where
    (TcK x b1) == (TcK y b4) = x == y
    (HypK x b1) == (HypK y b4) = x == y
    (CheckK x b1) == (CheckK y b4) = x == y
    x == y = False
    
instance Ord TCstr where
    compare (TcK x b1) (TcK y b4) = mconcat [compare x y]
    compare (HypK x b1) (HypK y b4) = mconcat [compare x y]
    compare (CheckK x b1) (CheckK y b4) = mconcat [compare x y]
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)

isValidTcCstr (IsValid {}) = True
isValidTcCstr (NotEqual {}) = True
isValidTcCstr _ = False

ppExprTy e = do
    ppe <- pp e
    ppl <- pp (loc e)
    returnS $ ppe <+> text "::" <+> ppl
ppVarTy v = ppExprTy (varExpr v)

instance (DebugM m) => PP m [(IsConst,Either Expr Type,IsVariadic)] where
    pp xs = liftM (parens . sepBy comma) (mapM aux xs)
      where
        aux (x,y,z) = do
            y' <- eitherM ppExprTy pp y
            returnS $ ppConst x $ ppVariadic y' z

instance (DebugM m) => PP m TcCstr where
    pp (TDec k es n ts x) = do
        ppk <- pp k
        ppes <- pp (isJust es)
        ppn <- pp n
        ppts <- (mapM pp ts) 
        ppx <- pp x
        returnS $ text "tdec" <+> ppk <+> ppes <+> ppn <+> sepBy space ppts <+> char '=' <+> ppx
    pp (PDec k es n specs ts r x) = do
        ppk <- pp k
        ppes <- pp (isJust es)
        ppr <- pp r
        ppn <- pp n
        ppspecs <- mapM pp $ maybe [] id specs
        ppts <- pp ts
        ppx <- pp x
        returnS $ ppk <+> ppes <+> ppr <+> ppn <+> abrackets (sepBy comma ppspecs) <+> ppts <+> char '=' <+> ppx
    pp (Equals t1 t2) = do
        pp1 <- pp t1
        pp2 <- pp t2
        returnS $ text "equals" <+> pp1 <+> pp2
    pp (Coerces bvs e1 v2) = do
        ppbvs <- pp bvs
        pp1 <- ppExprTy e1
        pp2 <- ppVarTy v2
        returnS $ text "coerces" <+> ppbvs <+> pp1 <+> pp2
    pp (CoercesLit e) = do
        ppe <- ppExprTy e
        returnS $ text "coerceslit" <+> ppe
--    pp (CoercesN exs) = do
--        pp1 <- (mapM (ppExprTy . fst) exs)
--        pp2 <- (mapM (ppVarTy . snd) exs)
--        returnS $ text "coercesn" <+> sepBy comma pp1 <+> char '=' <+> sepBy comma pp2
    pp (Unifies t1 t2) = do
        pp1 <- pp t1
        pp2 <- pp t2
        returnS $ text "unifies" <+> pp1 <+> pp2
    pp (Assigns t1 t2) = do
        pp1 <- pp t1
        pp2 <- pp t2
        returnS $ text "assigns" <+> pp1 <+> pp2
    pp (SupportedPrint ts xs) = do
        ppts <- mapM pp ts
        ppxs <- mapM pp xs
        returnS $ text "print" <+> sepBy space ppts <+> sepBy space ppxs
    pp (ProjectStruct t a x) = do
        ppt <- pp t
        ppa <- pp a
        ppx <- pp x
        returnS $ ppt <> char '.' <> ppa <+> char '=' <+> ppx
    pp (ProjectMatrix t as x) = do
        pp1 <- pp t
        pp2 <- mapM pp as
        pp3 <- pp x
        returnS $ pp1 <> brackets (sepBy comma pp2) <+> char '=' <+> pp3
--    pp (MultipleSubstitutions ko v s) = do
--        ppko <- pp ko
--        pp1 <- pp v
--        let f2 (x,y,z) = do
--            ppx <- pp x
--            ppy <- pp y
--            ppz <- pp z
--            returnS $ ppx $+$ nest 4 (text "=>" $+$ ppy <+> text ":" <+> ppz)
--        pp2 <- (mapM f2 s)
--        returnS $ text "multiplesubstitutions" <+> ppko <+> pp1 <+> vcat pp2
    pp (MatchTypeDimension d sz) = do
        pp1 <- pp d
        pp2 <- pp sz
        returnS $ text "matchtypedimension" <+> pp1 <+> pp2
    pp (IsValid c) = liftM (text "isvalid" <+>) (pp c)
    pp (NotEqual e1 e2) = do
        pp1 <- pp e1
        pp2 <- pp e2
        returnS $ text "not equal" <+> pp1 <+> pp2
    pp (TypeBase t b) = do
        ppt <- pp t
        ppb <- pp b
        returnS $ text "typebase" <+> ppt <+> ppb
    pp (IsPublic b e) = do
        ppb <- pp b
        ppe <- pp e
        returnS $ text "ispublic" <+> ppb <+> ppe
    pp (IsPrivate b e) = do
        ppb <- pp b
        ppe <- pp e
        returnS $ text "isprivate" <+> ppb <+> ppe
    pp (Resolve e) = liftM (text "resolve" <+>) (pp e)
    pp (Default szs e) = do
        pp1 <- pp szs
        pp2 <- ppExprTy e
        returnS $ text "default" <+> pp1 <+> pp2
    pp (ToMultiset t r) = do
        ppt <- pp t
        ppr <- pp r
        returnS $ text "tomultiset" <+> ppt <+> ppr
    pp (ToSet t r) = do
        ppt <- pp t
        ppr <- pp r
        returnS $ text "toset" <+> ppt <+> ppr

instance (DebugM m) => PP m CheckCstr where
    pp (CheckAssertion c) = liftM (text "checkAssertion" <+>) (pp c)

instance (DebugM m) => PP m HypCstr where
    pp (HypCondition c) = do
        pp1 <- pp c
        returnS $ text "hypothesis" <+> pp1
    pp (HypNotCondition c) = do
        pp1 <- pp c
        returnS $ text "hypothesis" <+> char '!' <> pp1
    pp (HypEqual e1 e2) = do
        pp1 <- pp e1
        pp2 <- pp e2
        returnS $ text "hypothesis" <+> pp1 <+> text "==" <+> pp2

instance (DebugM m) => PP m TCstr where
    pp (TcK k _) = pp k
    pp (CheckK c _) = pp c
    pp (HypK h _) = pp h

data ArrayProj
    = ArraySlice ArrayIndex ArrayIndex
    | ArrayIdx ArrayIndex
  deriving (Data,Typeable,Show,Generic)

instance Binary ArrayProj
instance Hashable ArrayProj
    
instance Eq ArrayProj where
    (ArraySlice i1 i2) == (ArraySlice i3 i4) = i1 == i3 && i2 == i4
    (ArrayIdx w1) == (ArrayIdx w2) = w1 == w2
    x == y = False
instance Ord ArrayProj where
    compare (ArraySlice i1 i2) (ArraySlice i3 i4) = compare i1 i3 `mappend` compare i2 i4
    compare (ArrayIdx w1) (ArrayIdx w2) = compare w1 w2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)
    
instance (DebugM m) => PP m ArrayProj where
    pp (ArraySlice i1 i2) = do
        pp1 <- pp i1
        pp2 <- pp i2
        returnS $ pp1 <> char ':' <> pp2
    pp (ArrayIdx w) = pp w
    
instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m ArrayProj where
    traverseVars f (ArraySlice i1 i2) = do
        i1' <- f i1
        i2' <- f i2
        returnS $ ArraySlice i1' i2'
    traverseVars f (ArrayIdx w) = do
        w' <- f w
        returnS $ ArrayIdx w'
    
instance (DebugM m) => PP m [Type] where
    pp xs = do
        pxs <- mapM pp xs
        returnS $ brackets $ sepBy comma pxs
    
instance (DebugM m) => PP m [(Type,IsVariadic)] where
    pp xs = do
        pp1 <- mapM (ppVariadicArg pp) xs
        returnS $ parens $ sepBy comma pp1
instance (DebugM m) => PP m [(Constrained Var,IsVariadic)] where
    pp xs = do
        pp1 <- mapM (ppVariadicArg pp) xs
        returnS $ parens $ sepBy comma pp1
    
instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m [Type] where
    traverseVars f xs = mapM f xs
    
instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m [(Type, IsVariadic)] where
    traverseVars f xs = mapM f xs
instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m [(Constrained Var, IsVariadic)] where
    traverseVars f xs = mapM f xs
    
data ArrayIndex
    = NoArrayIndex
    | DynArrayIndex Expr
  deriving (Data,Typeable,Show,Generic)
  
instance Binary ArrayIndex
instance Hashable ArrayIndex

instance Eq ArrayIndex where
    NoArrayIndex == NoArrayIndex = True
    (DynArrayIndex e1) == (DynArrayIndex e2) = e1 == e2
    x == y = False
instance Ord ArrayIndex where
    compare NoArrayIndex NoArrayIndex = EQ
    compare (DynArrayIndex e1) (DynArrayIndex e2) = compare e1 e2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)
  
instance (DebugM m) => PP m ArrayIndex where
    pp NoArrayIndex = returnS PP.empty
    pp (DynArrayIndex e) = pp e
    
instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m ArrayIndex where
    traverseVars f NoArrayIndex = returnS NoArrayIndex
    traverseVars f (DynArrayIndex e) = do
        e' <- f e
        returnS $ DynArrayIndex e'

arrayIndexExpr :: ArrayIndex -> Expr
arrayIndexExpr (DynArrayIndex e) = e

indexExpr :: Word64 -> Expression iden Type
indexExpr i = LitPExpr (BaseT index) $ IntLit (BaseT index) $ toInteger i

intExpr :: Type -> Integer -> Expression iden Type
intExpr t i = LitPExpr t $ IntLit t i

floatExpr :: Type -> Double -> Expression iden Type
floatExpr t i = LitPExpr t $ FloatLit t i

stringExpr :: String -> Expression iden Type
stringExpr s = LitPExpr (BaseT string) $ StringLit (BaseT string) s

trueExpr :: CondExpression iden Type
trueExpr = (LitPExpr (BaseT bool) $ BoolLit (BaseT bool) True)

falseExpr :: CondExpression iden Type
falseExpr = (LitPExpr (BaseT bool) $ BoolLit (BaseT bool) False)

indexExprLoc :: Location loc => loc -> Word64 -> Expression iden (Typed loc)
indexExprLoc l i = (fmap (Typed l) $ indexExpr i)

instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m TcCstr where
    traverseVars f (TDec k e n args x) = do
        k' <- f k
        e' <- mapM (mapM f) e
        n' <- f n
        args' <- mapM f args
        x' <- f x
        returnS $ TDec k' e' n' args' x'
    traverseVars f (PDec k e n ts args ret x) = do
        k' <- f k
        e' <- mapM (mapM f) e
        n' <- f n
        x' <- f x
        ts' <- mapM (mapM f) ts
        args' <- mapM f args
        ret' <- f ret
        returnS $ PDec k' e' n' ts' args' ret' x'
    traverseVars f (Equals t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        returnS $ Equals t1' t2'
    traverseVars f (Coerces bvs e1 v2) = do
        bvs' <- f bvs
        e1' <- f e1
        v2' <- {-inLHS False $ -}f v2
        returnS $ Coerces bvs' e1' v2'
--    traverseVars f (CoercesN exs) = do
--        exs' <- mapM (\(x,y) -> do { x' <- f x; y' <- {-inLHS False $ -}f y; returnS (x',y') }) exs
--        returnS $ CoercesN exs'
    traverseVars f (CoercesLit e) = do
        e' <- f e
        returnS $ CoercesLit e'
    traverseVars f (Unifies t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        returnS $ Unifies t1' t2'
    traverseVars f (Assigns t1 t2) = do
        t1' <- inLHS False $ f t1
        t2' <- f t2
        returnS $ Assigns t1' t2'
    traverseVars f (SupportedPrint ts xs) = do
        ts' <- mapM f ts
        xs' <- inLHS False $ mapM f xs
        returnS $ SupportedPrint ts' xs'
    traverseVars f (ProjectStruct t a x) = do
        t' <- f t
        a' <- f a
        x' <- f x
        returnS $ ProjectStruct t' a' x'
    traverseVars f (ProjectMatrix t is x) = do
        t' <- f t
        is' <- mapM f is
        x' <- f x
        returnS $ ProjectMatrix t' is' x'
--    traverseVars f (MultipleSubstitutions ko v ss) = do
--        ko' <- f ko
--        v' <- f v
--        ss' <- mapM (liftM (\(x,y,z) -> (x,y,mapSet unVIden z)) . f . (\(x,y,z) -> (x,y,mapSet VIden z))) ss
--        returnS $ MultipleSubstitutions ko' v' ss'
    traverseVars f (MatchTypeDimension t d) = do
        t' <- f t
        d' <- f d
        returnS $ MatchTypeDimension t' d'
    traverseVars f (IsValid c) = do
        c' <- f c
        returnS $ IsValid c'
    traverseVars f (NotEqual e1 e2) = do
        e1' <- f e1
        e2' <- f e2
        returnS $ NotEqual e1' e2'
    traverseVars f (IsPublic b c) = do
        b' <- f b
        c' <- f c
        returnS $ IsPublic b' c'
    traverseVars f (IsPrivate b c) = do
        b' <- f b
        c' <- f c
        returnS $ IsPrivate b' c'
    traverseVars f (Resolve t) = do
        t' <- f t
        returnS $ Resolve t'
    traverseVars f (Default szs t) = do
        szs' <- mapM f szs
        t' <- f t
        returnS $ Default szs' t'
    traverseVars f (ToMultiset t r) = do
        t' <- f t
        r' <- f r
        returnS $ ToMultiset t' r'
    traverseVars f (ToSet t r) = do
        t' <- f t
        r' <- f r
        returnS $ ToSet t' r'
    traverseVars f (TypeBase t b) = do
        t' <- f t
        b' <- f b
        returnS $ TypeBase t' b'

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m CheckCstr where
    traverseVars f (CheckAssertion c) = do
        c' <- f c
        returnS $ CheckAssertion c'

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m HypCstr where
    traverseVars f (HypCondition c) = do
        c' <- f c
        returnS $ HypCondition c'
    traverseVars f (HypNotCondition c) = do
        c' <- f c
        returnS $ HypNotCondition c'
    traverseVars f (HypEqual e1 e2) = do
        e1' <- f e1
        e2' <- f e2
        returnS $ HypEqual e1' e2'

instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m TCstr where
    traverseVars f (TcK k st) = do
        k' <- f k
        returnS $ TcK k' st
    traverseVars f (CheckK k st) = do
        k' <- f k
        returnS $ CheckK k' st
    traverseVars f (HypK k st) = do
        k' <- f k
        returnS $ HypK k' st

type GCstrGraph = Gr LocGCstr ()
type LocGCstr = Loc Position GCstr

type TCstrGraph = Gr LocTCstr ()
type LocTCstr = Loc Position TCstr

-- | Template constraint dictionary
-- a dictionary with a set of inferred constraints and resolved constraints
data TDict = TDict
    { tCstrs :: GCstrGraph -- a list of constraints
    , tChoices :: (Set Int) -- set of choice constraints that have already been branched
    , tSubsts :: TSubsts -- variable substitions
    , tRec :: ModuleTcEnv -- recursive environment
    -- this may be important because of nested dictionaries
    , tSolved :: (Map LocGCstr Bool) -- constraints already solved and (True=inferred constraint)
    }
  deriving (Typeable,Eq,Data,Ord,Show,Generic)
instance Hashable TDict


-- A dictionary with pure (unevaluated) constraints
data PureTDict = PureTDict
    { pureCstrs :: TCstrGraph
    , pureSubsts :: TSubsts
    , pureRec :: ModuleTcEnv
    }
  deriving (Typeable,Eq,Data,Ord,Show,Generic)
instance Hashable PureTDict
instance Binary PureTDict

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m TCstrGraph where
    traverseVars f g = nmapM f g

instance (DebugM m, GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m PureTDict where
    traverseVars f (PureTDict ks ss rec) = do
        ks' <- f ks
        ss' <- f ss
        rec' <- f rec
        returnS $ PureTDict ks' ss' rec'

fromPureTDict :: MonadIO m => PureTDict -> TcM m TDict
fromPureTDict (PureTDict g ss rec) = do
    g' <- fromPureCstrs g
    returnS $ TDict g' Set.empty ss rec Map.empty

fromPureCstrs :: MonadIO m => TCstrGraph -> TcM m GCstrGraph
fromPureCstrs g = do
    (g',is) <- runStateT (mapGrM newGCstr g) Map.empty
    mapGrM (go g' is) g'
  where
    go g' is (ins,j,x,outs) = do
        ins' <- fmapSndM (look g' is) ins
        outs' <- fmapSndM (look g' is) outs
        returnS $ (ins',j,x,outs')
    look g' is i = case Map.lookup i is of
        Just x -> returnS x
        Nothing -> do
            ppg <- ppr g
            ppg' <- ppr g'
            error $ "fromPureCstrs: failed to look up " ++ show i ++ " in " ++ show is ++ "\n" ++ ppg ++ "\n" ++ ppg'
    newGCstr (ins,i,Loc l k,outs) = do
        mn <- lift $ newModuleTyVarId
        let j = hashModuleTyVarId mn
        State.modify $ \is -> Map.insert i j is
#if INCREMENTAL
        st <- lift $ liftIO $ newIdRef mn Unevaluated
        returnS (ins,j,Loc l $ IOCstr k st,outs)
#else
        returnS (ins,j,Loc l $ IdCstr k mn,outs)
#endif

toPureCstrs :: GCstrGraph -> Map LocGCstr Bool -> TCstrGraph
toPureCstrs ks solved = unionGr g1 g2
    where
    g1 = nmap (fmap kCstr) ks
    inferred = Map.keys $ Map.filter id solved
    g2 = Graph.mkGraph (map (\x -> (gCstrId $ unLoc x,fmap kCstr x)) inferred) []

toPureTDict :: TDict -> PureTDict
toPureTDict (TDict ks _ ss rec solved) = PureTDict (toPureCstrs ks solved) ss rec

flattenGCstrGraph :: GCstrGraph -> [LocGCstr]
flattenGCstrGraph = map snd . labNodes

flattenGCstrGraphSet :: GCstrGraph -> Set LocGCstr
flattenGCstrGraphSet = Set.fromList . flattenGCstrGraph

-- | mappings from variables to current substitution
newtype TSubsts = TSubsts { unTSubsts :: Map VarIdentifier Type } deriving (Eq,Show,Ord,Typeable,Data,Generic)
instance Binary TSubsts
instance Hashable TSubsts

instance Monoid TSubsts where
    mempty = TSubsts Map.empty
    mappend (TSubsts x) (TSubsts y) = TSubsts (x `Map.union` y)

instance (DebugM m) => PP m TSubsts where
    pp = ppTSubsts

instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m TSubsts where
    traverseVars f (TSubsts xs) = varsBlock $ liftM (TSubsts . Map.fromList) $ aux $ Map.toList xs
        where
        aux [] = returnS []
        aux ((k,v):xs) = do
            VIden k' <- inLHS False $ f (VIden k::GIdentifier)
            v' <- f v
            xs' <- aux xs
            returnS ((k',v'):xs')

emptyTDict :: TDict
emptyTDict = TDict Graph.empty Set.empty emptyTSubsts mempty Map.empty

emptyPureTDict :: PureTDict
emptyPureTDict = PureTDict Graph.empty emptyTSubsts mempty

emptyTSubsts :: TSubsts
emptyTSubsts = TSubsts Map.empty

instance (Vars GIdentifier m loc,Vars GIdentifier m a) => Vars GIdentifier m (Loc loc a) where
    traverseVars f (Loc l a) = do
        l' <- f l
        a' <- f a
        returnS $ Loc l' a'

newModuleTyVarId :: MonadIO m => TcM m ModuleTyVarId
newModuleTyVarId = do
    i <- liftIO newTyVarId
    m <- State.gets (fmap fst . fst . moduleCount)
    returnS $ ModuleTyVarId m i

freshVarId :: MonadIO m => Identifier -> Maybe Doc -> TcM m VarIdentifier
freshVarId n doc = do
    i <- liftIO newTyVarId
    mn <- State.gets (fmap fst . fst . moduleCount)
    let v' = VarIdentifier n mn (Just i) True True doc
    returnS v'

freeVarId :: MonadIO m => String -> Identifier -> Bool -> Maybe Doc -> TcM m VarIdentifier
freeVarId msg n isVariadic doc = do
    v <- freshVarId n doc
    addFree (msg++" freeVarId") v isVariadic
    returnS v

type Frees = Map VarIdentifier IsVariadic

addFree :: MonadIO m => String -> VarIdentifier -> Bool -> TcM m ()
addFree msg n isVariadic = do
    debugTc $ do
        ppn <- ppr n
--        olds <- State.gets localFrees
--        ppolds <- ppr olds
        liftIO $ putStrLn $ "addFree " ++ msg ++ " " ++ ppn ++ " " ++ pprid isVariadic -- ++ " to " ++ ppolds
    State.modify $ \env -> env { localFrees = Map.insert n isVariadic (localFrees env) }

removeFree :: MonadIO m => String -> VarIdentifier -> TcM m ()
removeFree msg n = do
    debugTc $ do
        ppn <- ppr n
--        olds <- State.gets localFrees
--        ppolds <- ppr olds
        liftIO $ putStrLn $ "removeFree " ++ msg ++ " " ++ ppn -- ++ " from " ++ ppolds
    State.modify $ \env -> env { localFrees = Map.delete n (localFrees env) }

instance (DebugM m) => PP m TDict where
    pp dict = do
        pp1 <- ppGrM pp (const $ returnS PP.empty) $ tCstrs dict
        pp2 <- ppTSubsts (tSubsts dict)
        returnS $ text "Constraints:" $+$ nest 4 pp1
              $+$ text "Substitutions:" $+$ nest 4 pp2

instance (DebugM m) => PP m PureTDict where
    pp dict = do
        pp1 <- ppGrM pp (const $ returnS PP.empty) $ pureCstrs dict
        pp2 <- ppTSubsts (pureSubsts dict)
        returnS $ text "Constraints:" $+$ nest 4 pp1
              $+$ text "Substitutions:" $+$ nest 4 pp2

ppConstraints :: MonadIO m => GCstrGraph -> TcM m Doc
ppConstraints d = do
    ss <- ppGrM ppLocGCstr (const $ returnS PP.empty) d
    returnS ss

ppLocGCstr :: MonadIO m => LocGCstr -> TcM m Doc
#if INCREMENTAL
ppLocGCstr (Loc l c) = do
    s <- readCstrStatus l c
    pre <- pp c
    case s of
        Evaluated rest frees infer t -> do
            ppf <- pp frees
            returnS $ pre <+> char '=' <+> text (show t) <+> text "with frees" <+> ppf
        Unevaluated -> returnS $ pre
        Erroneous err -> returnS $ pre <+> char '=' <+> if isHaltError err then text "HALT" else text "ERROR"
#else
ppLocGCstr (Loc l c) = pp c
#endif

#if INCREMENTAL
readCstrStatus :: MonadIO m => Position -> GCstr -> TcM m TCstrStatus
readCstrStatus p iok = do
    solved <- State.gets cstrCache
    case Map.lookup (Loc p iok) solved of
        Just st -> returnS st
        Nothing -> liftIO $ readIdRef (kStatus iok)
#endif

#if INCREMENTAL
writeCstrStatus :: MonadIO m => Position -> GCstr -> TCstrStatus -> TcM m ()
writeCstrStatus p iok st = do
    delaySolve <- State.gets solveToCache
    if delaySolve
        then State.modify $ \e -> e { cstrCache = Map.insert (Loc p iok) st (cstrCache e) }
#else
withRecordSols :: MonadIO m => TcM m a -> TcM m a
withRecordSols m = do
    old <- State.gets recordSols
    osols <- State.gets cstrSols
    State.modify $ \e -> e { recordSols = True }
    x <- m
    State.modify $ \e -> e { recordSols = old, cstrSols = osols }
    returnS x
    
writeCstrSol :: MonadIO m => Position -> GCstr -> ShowOrdDyn -> TcM m ()
writeCstrSol p iok sol = do
    ok <- State.gets recordSols
    when ok $ State.modify $ \e -> e { cstrSols = Map.insert (Loc p iok) sol (cstrSols e) }
#endif

data VarIdentifier = VarIdentifier
        { varIdBase :: Identifier
        , varIdModule :: (Maybe (Identifier,TyVarId))
        , varIdUniq :: (Maybe TyVarId)
        , varIdWrite :: Bool -- if the variable can be written
        , varIdRead :: Bool -- if the variable can be read
        , varIdPretty :: (Maybe Doc) -- for free variables introduced by typechecking
        }
    deriving (Typeable,Data,Show,Generic)

instance Binary VarIdentifier

instance Eq VarIdentifier where
    v1 == v2 = varIdUniq v1 == varIdUniq v2 && varIdBase v1 == varIdBase v2 && varIdModule v1 == varIdModule v2
instance Ord VarIdentifier where
    compare v1 v2 = mconcat [varIdBase v1 `compare` varIdBase v2,varIdUniq v1 `compare` varIdUniq v2,varIdModule v1 `compare` varIdModule v2]

varRead :: VarName VarIdentifier loc -> Bool
varRead (VarName _ n) = varIdRead n

varWrite :: VarName VarIdentifier loc -> Bool
varWrite (VarName _ n) = varIdWrite n

varIdTok :: VarIdentifier -> Bool
varIdTok v = not (varIdRead v) && not (varIdWrite v)

mkVarId :: Identifier -> VarIdentifier
mkVarId s = VarIdentifier s Nothing Nothing True True Nothing

instance Monad m => DebugM (TcM m) where
    isDebug = liftM debug askOpts

instance DebugM m => PP m VarIdentifier where
    pp v = do
        is <- isDebug
        ppVarId is v

ppVarId :: Monad m => Bool -> VarIdentifier -> m Doc
ppVarId doDebug v = liftM (ppPretty . ppRWs) (ppVarId' v)
  where
    pread = if varIdRead v then "Read" else "NoRead"
    pwrite = if varIdWrite v then "Write" else "NoWrite"
    f (x,blk) = do
        pp1 <- pp blk
        returnS $ text x <> char '.' <> pp1 <> char '.'
    ppVarId' (VarIdentifier n m Nothing _ _ _) = do
        ppo <- ppOpt m f
        returnS $ ppo <> text n
    ppVarId' (VarIdentifier n m (Just i) _ _ _) = do
        ppo <- ppOpt m f
        ppi <- pp i
        returnS $ ppo <> text n <> char '_' <> ppi
    ppRWs x = if doDebug
        then x <> char '#' <> text pread <> text pwrite
        else x
    ppPretty x = case varIdPretty v of
        Just s -> if doDebug
            then x <> char '#' <> s
            else s
        Nothing -> x

newtype TyVarId = TyVarId Integer deriving (Eq,Ord,Data,Generic)
instance Show TyVarId where
    show (TyVarId i) = show i
instance Monad m => PP m TyVarId where
    pp (TyVarId i) = pp i
instance Binary TyVarId
instance Hashable TyVarId where
    hashWithSalt i (TyVarId x) = hashWithSalt i x

instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m TyVarId where
    traverseVars f x = returnS x

uniqTyVarId :: IORef Integer
uniqTyVarId = unsafePerformIO (newIORef 0)
{-# NOINLINE uniqTyVarId #-}

backupTyVarId :: IO TyVarId
backupTyVarId = do
    ti <- readIORef uniqTyVarId
    resetTyVarId
    returnS $ TyVarId ti

restoreTyVarId :: TyVarId -> IO ()
restoreTyVarId (TyVarId ti) = do
    atomicModifyIORef' uniqTyVarId $ \x -> (ti,ti)
    returnS ()

resetTyVarId :: IO ()
resetTyVarId = do
    atomicModifyIORef' uniqTyVarId $ \x -> (0,0)
    returnS ()

newTyVarId :: IO TyVarId
newTyVarId = do
  r <- atomicModifyIORef' uniqTyVarId $ \x -> let z = x+1 in (z,z)
  returnS (TyVarId r)

hashTyVarId :: TyVarId -> Int
hashTyVarId (TyVarId i) = I# (hashInteger i)

secTypeKind :: SecType -> KindType
secTypeKind Public = PublicK
secTypeKind (Private _ k) = PrivateK k
secTypeKind (SVar _ k) = k

data SecType
    = Public -- ^ public domain
    | Private -- ^ private domain
        GIdentifier -- ^ domain
        GIdentifier -- ^ kind
    | SVar VarIdentifier KindType
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary SecType
instance Hashable SecType

data KindType
    = PublicK
    | PrivateK GIdentifier -- a known kind
    | KVar VarIdentifier (Maybe KindClass) -- a kind variable (bool = is only private)
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary KindType
instance Hashable KindType

kindClass :: KindType -> Maybe KindClass
kindClass PublicK = Nothing
kindClass (PrivateK _) = Just NonPublicClass
kindClass (KVar _ c) = c

isPrivateKind :: KindType -> Bool
isPrivateKind k = case kindClass k of
    Just NonPublicClass -> True
    Nothing -> False

tyDecClass :: Type -> DecClass
tyDecClass (DecT (DecType _ _ _ _ _ _ (ProcType _ _ _ _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ (FunType _ _ _ _ _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ (StructType _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ (AxiomType _ _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ (LemmaType _ _ _ _ _ _ cl))) = cl
tyDecClass t = error $ "tyDecClass: " ++ show t

tyIsAnn t = let (DecClass b _ _ _) = tyDecClass t in b
tyIsInline t = let (DecClass _ b _ _) = tyDecClass t in b

decTypeFrees :: DecType -> Frees
decTypeFrees (DecType _ _ _ hctx bctx _ _) = Map.unionWith (||) (dCtxFrees hctx) (dCtxFrees bctx)

decTypeId :: DecType -> Maybe (GIdentifier,ModuleTyVarId)
decTypeId d = case (decTypeDecId d,decTypeTyVarId d) of
    (Just x,Just y) -> Just (x,y)
    otherwise -> Nothing
    
decTypeDecId :: DecType -> Maybe GIdentifier
decTypeDecId (DecType _ _ _ _ _ _ d) = decTypeDecId' d
    where
    decTypeDecId' (ProcType _ o _ _ _ _ _) = Just $ funit o
    decTypeDecId' (LemmaType _ _ p _ _ _ _) = Just $ funit p
    decTypeDecId' (FunType _ _ o _ _ _ _ _) = Just $ funit o
    decTypeDecId' (StructType _ s _ _) = Just $ funit s
    decTypeDecId' (AxiomType _ _ _ _ _) = Nothing
decTypeDecId d = Nothing

isLeakType :: Type -> Bool
isLeakType (DecT d) = isLeakDec d

isLeakDec :: DecType -> Bool
isLeakDec (DecType _ _ _ _ _ _ i) = isLeakInnerDec i

isLeakInnerDec :: InnerDecType -> Bool
isLeakInnerDec (ProcType {}) = False
isLeakInnerDec (FunType isLeak _ _ _ _ _ _ _) = isLeak
isLeakInnerDec (StructType {}) = False
isLeakInnerDec (AxiomType isLeak _ _ _ _) = isLeak
isLeakInnerDec (LemmaType isLeak _ _ _ _ _ _) = isLeak

decTyKind :: DecType -> DecKind
decTyKind (DecType _ _ _ _ _ _ i) = iDecTyKind i

iDecTyKind :: InnerDecType -> DecKind
iDecTyKind (ProcType {}) = PKind
iDecTyKind (FunType {}) = FKind
iDecTyKind (AxiomType {}) = AKind
iDecTyKind (StructType {}) = TKind
iDecTyKind (LemmaType {}) = LKind

data DecCtx = DecCtx
    { dCtxExplicit :: (Maybe (Map ModuleTyVarId VarIdentifier))
    , dCtxDict :: PureTDict
    , dCtxFrees :: Frees }
  deriving (Typeable,Show,Data,Generic,Eq,Ord)
instance Binary DecCtx
instance Hashable DecCtx

implicitDecCtx :: DecCtx
implicitDecCtx = DecCtx Nothing emptyPureTDict Map.empty

explicitDecCtx :: DecCtx
explicitDecCtx = DecCtx (Just Map.empty) emptyPureTDict Map.empty

ppContext hasCtx = if isJust (hasCtx) then text "context" else text "implicit"

instance (DebugM m) => PP m DecCtx where
    pp (DecCtx has dict frees) = do
        ppfrees <- pp frees
        ppd <- pp dict
        returnS $ ppContext has $+$ text "Frees:" <+> ppfrees $+$ ppd

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m DecCtx where
    traverseVars f (DecCtx has dict frees) = do
        has' <- mapM (liftM (Map.fromList . map (mapSnd unVIden)) . mapM (f . mapSnd VIden) . Map.toList) has
        frees' <- liftM Map.fromList $ mapM (liftM (mapFst unVIden) . f . mapFst VIden) $ Map.toList frees
        dict' <- f dict
        returnS $ DecCtx has' dict' frees'

data DecTypeK
    = DecTypeInst ModuleTyVarId IsRec  -- instance declaration (for template instantiations)
    | DecTypeCtx                -- context declaration
    | DecTypeOri IsRec            -- original declarations
  deriving (Typeable,Show,Data,Generic,Eq,Ord)
instance Binary DecTypeK
instance Hashable DecTypeK

-- annotation if declaration is a recursive invocation
type IsRec = Bool

ppIsRec False = PP.empty
ppIsRec True = text "rec"

instance Monad m => PP m DecTypeK where
    pp (DecTypeCtx) = returnS $ text "context"
    pp (DecTypeOri isRec) = returnS $ text "original" <+> ppIsRec isRec
    pp (DecTypeInst i isRec) = returnS $ text "instance" <+> ppid i <+> ppIsRec isRec

decTypeKind :: DecType -> DecTypeK
decTypeKind (DecType _ k _ _ _ _ _) = k
decTypeKind (DVar v) = error $ "decTypeKind: " ++ show v

data DecType
    = DecType -- ^ top-level declaration (used for template declaration and also for non-templates to store substitutions)
        ModuleTyVarId -- ^ unique template declaration id
        DecTypeK
        [(Constrained Var,IsVariadic)] -- ^ template variables
        DecCtx -- ^ header
        DecCtx -- ^ body
        [(Type,IsVariadic)] -- ^ template specializations
        InnerDecType -- ^ template's type
    | DVar -- declaration variable
        VarIdentifier
  deriving (Typeable,Show,Data,Generic)

data InnerDecType
    = ProcType -- ^ procedure type
        Position
        PIdentifier
        [(Bool,Var,IsVariadic)] -- typed procedure arguments
        Type -- returnS type
        [ProcedureAnnotation GIdentifier (Typed Position)] -- ^ the procedure's annotations
        (Maybe [Statement GIdentifier (Typed Position)]) -- ^ the procedure's body
        DecClass -- the type of procedure
    | FunType -- ^ procedure type
        Bool -- is leakage function
        Position
        PIdentifier
        [(Bool,Var,IsVariadic)] -- typed function arguments
        Type -- returnS type
        [ProcedureAnnotation GIdentifier (Typed Position)] -- ^ the function's annotations
        (Maybe (Expression GIdentifier (Typed Position))) -- ^ the function's body
        DecClass -- the type of function
    | StructType -- ^ Struct type
        Position -- ^ location of the procedure declaration
        SIdentifier
        (Maybe [Attr]) -- ^ typed arguments
        DecClass -- the type of struct
    | AxiomType
        Bool -- is leakage axiom
        Position
        [(Bool,Var,IsVariadic)] -- typed function arguments
        [ProcedureAnnotation GIdentifier (Typed Position)] -- ^ the procedure's annotations
        DecClass
    | LemmaType -- ^ lemma type
        Bool -- is leakage
        Position
        PIdentifier -- lemma's name
        [(Bool,Var,IsVariadic)] -- typed lemma arguments
        [ProcedureAnnotation GIdentifier (Typed Position)] -- ^ the lemma's annotations
        (Maybe (Maybe [Statement GIdentifier (Typed Position)])) -- ^ the lemma's body
        DecClass -- the type of lemma        
  deriving (Typeable,Show,Data,Generic,Eq,Ord)

isLeakIDecType :: InnerDecType -> Bool
isLeakIDecType (ProcType {}) = False
isLeakIDecType (FunType isLeak _ _ _ _ _ _ _) = isLeak
isLeakIDecType (StructType {}) = False
isLeakIDecType (AxiomType isLeak _ _ _ _) = isLeak
isLeakIDecType (LemmaType isLeak _ _ _ _ _ _) = isLeak

iDecArgs :: InnerDecType -> [(Bool,Var,IsVariadic)]
iDecArgs (LemmaType _ _ _ as _ _ _) = as
iDecArgs (AxiomType _ _ as _ _) = as
iDecArgs (StructType {}) = []
iDecArgs (FunType _ _ _ as _ _ _ _) = as
iDecArgs (ProcType _ _ as _ _ _ _) = as

isTemplateDecType :: DecType -> Bool
isTemplateDecType (DecType _ _ ts _ _ specs _) = not (null ts)
isTemplateDecType _ = False

isFunType :: Type -> Bool
isFunType (DecT d) = isFunDecType d
isFunType _ = False 

isFunDecType :: DecType -> Bool
isFunDecType (DecType _ _ _ _ _ specs (FunType {})) = True
isFunDecType _ = False

isFunInnerDecType :: InnerDecType -> Bool
isFunInnerDecType (FunType {}) = True
isFunInnerDecType _ = False

--isNonRecursiveDecType :: DecType -> Bool
--isNonRecursiveDecType (DecType i _ _ _ _ _ d) = not $ everything (||) (mkQ False aux) d
--    where
--    aux :: DecType -> Bool
--    aux (DecType _ (Just (j)) _ _ _ _ _) = i == j
--    aux d = False
--isNonRecursiveDecType d = False

instance Binary DecType
instance Hashable DecType
instance Binary InnerDecType
instance Hashable InnerDecType

instance Eq DecType where
    (DVar v1) == (DVar v2) = v1 == v2
    x == y = decTypeTyVarId x == decTypeTyVarId y
instance Ord DecType where
    compare (DVar v1) (DVar v2) = compare v1 v2
    compare x y = compare (decTypeTyVarId x) (decTypeTyVarId y)

data Constrained a = Constrained a (Maybe Cond)
  deriving (Typeable,Show,Data,Eq,Ord,Functor,Generic)

hasConstrained :: Constrained a -> Bool
hasConstrained (Constrained _ Nothing) = False
hasConstrained (Constrained _ (Just _)) = True

instance Binary a => Binary (Constrained a)
instance Hashable a => Hashable (Constrained a)

unConstrained :: Constrained a -> a
unConstrained (Constrained x c) = x

instance (DebugM m,PP m a) => PP m (Constrained a) where
    pp = ppConstrained pp

ppConstrained :: (DebugM m) => (a -> m Doc) -> Constrained a -> m Doc
ppConstrained f (Constrained t Nothing) = f t
ppConstrained f (Constrained t (Just c)) = do
    ft <- f t
    ppc <- pp c
    returnS $ ft <+> braces ppc

instance (DebugM m,GenVar VarIdentifier m,MonadIO m,Vars GIdentifier m a) => Vars GIdentifier m (Constrained a) where
    traverseVars f (Constrained t e) = do
        t' <- f t
        e' <- inRHS $ f e
        returnS $ Constrained t' e'

data BaseType
    = TyPrim Prim
    | TApp SIdentifier [(Type,IsVariadic)] DecType -- template type application
    | MSet ComplexType -- multiset type
    | Set ComplexType -- set type
    | BVar VarIdentifier (Maybe DataClass)
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary BaseType
instance Hashable BaseType

baseDataClass :: BaseType -> Maybe DataClass
baseDataClass (TyPrim p) = if isNumericPrimType p then Just NumericClass else Just PrimitiveClass
baseDataClass (TApp {}) = Nothing
baseDataClass (MSet {}) = Nothing
baseDataClass (Set {}) = Nothing
baseDataClass (BVar v k) = k

type CondExpression iden loc = (Expression iden loc)
type Cond = CondExpression GIdentifier Type

data ComplexType
    = CType -- ^ Compound SecreC type
        SecType -- ^ security type
        BaseType -- ^ data type
        Expr -- ^ dimension (default = 0, i.e., scalars)
    | CVar VarIdentifier Bool -- (isNotVoid flag)
    | Void -- ^ Empty type
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary ComplexType
instance Hashable ComplexType

data SysType
    = SysPush Type
    | SysRet Type
    | SysRef Type
    | SysCRef Type
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary SysType
instance Hashable SysType

data Type
    = NoType String -- ^ For locations with no associated type information
    | TType Bool -- ^ Type of complex types (isNotVoid)
    | DType -- ^ Type of declarations
    | BType (Maybe DataClass) -- ^ Type of base types
    | KType (Maybe KindClass) -- ^ Type of kinds
    | VAType Type Expr -- ^ Type of array types
    | StmtType (Set StmtClass) -- ^ Type of a @Statement@
    | ComplexT ComplexType
    | BaseT BaseType
    | SecT SecType
    | KindT KindType
    | DecT DecType
    | IDecT InnerDecType -- internal only
    | DecCtxT DecCtx -- internal only
    | TCstrT TCstr -- internal only
    | SysT SysType
    | VArrayT VArrayType -- for variadic array types
    | IdxT Expr -- for index expressions
    | WhileT DecClassVars DecClassVars -- read/write variables for while loops
--    | CondType Type Cond -- a type with an invariant
  deriving (Typeable,Show,Data,Eq,Ord,Generic)
  
instance Binary Type
instance Hashable Type

-- | Type arrays
data VArrayType
    = VAVal -- a type array value
        [Type] -- array elements
        Type -- type of array elements
    | VAVar VarIdentifier Type Expr -- a type array variable
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary VArrayType
instance Hashable VArrayType

vArraySize :: VArrayType -> Expr
vArraySize (VAVal xs _) = indexExpr $ toEnum $ length xs
vArraySize (VAVar _ _ sz) = sz

vArrayBase :: VArrayType -> Type
vArrayBase (VAVal xs b) = b
vArrayBase (VAVar _ b sz) = b

tyOf :: Type -> Type
tyOf (IdxT e) = loc e
tyOf (SecT s) = KindT (secTypeKind s)
tyOf (KindT k) = KType (kindClass k)
tyOf (ComplexT t) = TType (isNotVoid t)
tyOf (BaseT b) = BType $ baseDataClass b
tyOf (DecT _) = DType
tyOf (VArrayT (VAVal ts b)) = VAType b (indexExpr $ toEnum $ length ts)
tyOf (VArrayT (VAVar v b sz)) = VAType b sz
--tyOf (CondType t _) = tyOf t
tyOf t = error $ "unknown type for " ++ show t

--constrainedType :: Type -> Maybe Cond -> Type
--constrainedType t Nothing = t
--constrainedType t (Just c) = CondType t c

ppOf a b = a <+> text "::" <+> b
ppTyped (a,b) = do
    ppa <- pp a
    ppb <- pp b
    returnS $ ppa `ppOf` ppb
ppFrees xs = do
    ppxs <- mapM pp $ Set.toList xs
    returnS $ text "Free variables:" <+> sepBy comma ppxs

instance (DebugM m) => PP m VArrayType where
    pp (VAVal ts b) = do
        ppts <- mapM pp ts
        ppb <- pp b
        returnS $ brackets $ sepBy comma ppts <+> text "::" <+> ppb <> text "..." <> PP.int (length ts)
    pp (VAVar v b sz) = do
        ppv <- pp v
        ppb <- pp b
        ppsz <- pp sz
        returnS $ parens (ppv <+> text "::" <+> ppb <> text "..." <> parens ppsz)

instance (DebugM m) => PP m SecType where
    pp Public = returnS $ text "public"
    pp (Private d k) = pp d
    pp (SVar v k) = do
        ppv <- pp v
        ppk <- pp k
        returnS $ parens (ppv <+> text "::" <+> ppk)
        
ppAtt (Attribute t _ n szs) = do
    ppt <- pp t
    ppn <- pp n
    ppz <- pp szs
    returnS $ ppt <+> ppn <> ppz        

instance (DebugM m) => PP m DecType where
    pp (DecType did isrec vars hctx bctx specs body@(StructType _ n atts cl)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp3 <- pp hctx
        pp4 <- pp bctx
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp n
        pp7 <- mapM pp specs
        pp8 <- ppOpt atts (liftM (braces . vcat) . mapM ppAtt)
        pp9 <- pp cl
        returnS $ pp1 <+> pp2
            $+$ pp3 $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ text "struct" <+> pp6 <> abrackets (sepBy comma pp7) <+> pp8 $+$ pp9
    pp (DecType did isrec vars hctx bctx specs body@(ProcType _ n args ret ann stmts cl)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp3 <- pp hctx
        pp4 <- pp bctx
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp ret
        pp7 <- pp n
        pp70 <- mapM pp specs
        pp8 <- mapM ppConstArg args
        pp9 <- pp ann
        pp10 <- ppOpt stmts (liftM braces . pp)
        ppcl <- pp cl
        returnS $ pp1 <+> pp2
            $+$ pp3
            $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ pp6 <+> prefixOp (isOIden' n) pp7 <> abrackets (sepBy comma pp70) <> parens (sepBy comma pp8)
            $+$ pp9
            $+$ pp10
            $+$ ppcl
    pp (DecType did isrec vars hctx bctx specs body@(FunType isLeak _ n args ret ann stmts cl)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp3 <- pp hctx
        pp4 <- pp bctx
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp ret
        pp7 <- pp n
        pp70 <- mapM pp specs
        pp8 <- mapM ppConstArg args
        pp9 <- pp ann
        pp10 <- ppOpt stmts (liftM braces . pp)
        ppcl  <- pp cl
        returnS $ ppLeak (lkgBool isLeak) (pp1 <+> pp2
            $+$ pp3
            $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ pp6 <+> text "function" <+> prefixOp (isOIden' n) pp7 <> abrackets (sepBy comma pp70) <> parens (sepBy comma pp8)
            $+$ pp9
            $+$ pp10
            $+$ ppcl)
    pp (DecType did isrec vars hctx bctx specs body@(AxiomType isLeak _ args ann cl)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp3 <- pp hctx
        pp4 <- pp bctx
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp50 <- mapM pp specs
        pp6 <- mapM ppConstArg args
        pp7 <- pp ann
        ppcl <- pp cl
        returnS $ ppLeak (lkgBool isLeak) (pp1 <+> pp2
            $+$ pp3
            $+$ pp4
            $+$ text "axiom" <> abrackets (sepBy comma pp5) <> abrackets (sepBy comma pp50)
            <+> parens (sepBy comma $ pp6) $+$ pp7 $+$ ppcl)
    pp (DecType did isrec vars hctx bctx specs body@(LemmaType isLeak _ n args ann stmts cl)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp3 <- pp hctx
        pp4 <- pp bctx
        pp5 <- pp n
        pp6 <- mapM (ppVariadicArg ppTpltArg) vars
        pp60 <- mapM pp specs
        pp7 <- mapM ppConstArg args
        pp8 <- pp ann
        pp9 <- ppOpt stmts (liftM braces . pp)
        ppcl <- pp cl
        returnS $ ppLeak (lkgBool isLeak) (pp1 <+> pp2
            $+$ pp3
            $+$ pp4
            $+$ text "lemma" <+> pp5 <+> abrackets (sepBy comma pp6) <> abrackets (sepBy comma pp60)
            <+> parens (sepBy comma pp7)
            $+$ pp8
            $+$ pp9 $+$ ppcl)
    pp (DVar v) = pp v
    pp d = error $ "pp: " ++ show d

ppConstArg (isConst,(VarName t n),isVariadic) = do
    ppt <- pp t
    ppn <- pp n
    returnS $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)

prefixOp True = (text "operator" <+>)
prefixOp False = id

instance (DebugM m,Monad m) => PP m InnerDecType where
    pp (StructType _ n atts cl) = do
        ppn <- pp n
        ppo <- ppOpt atts (liftM (braces . vcat) . mapM ppAtt)
        returnS $ text "struct" <+> ppn <+> ppo
    pp (ProcType _ n args ret ann stmts _) = do
        ppret <- pp ret
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            returnS $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        returnS $ ppret <+> prefixOp (isOIden' n) ppn <> parens (sepBy comma pp1) $+$ ppann $+$ ppo
    pp (FunType isLeak _ n args ret ann stmts _) = do
        ppret <- pp ret
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            returnS $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        returnS $ ppLeak (lkgBool isLeak) (ppret <+> prefixOp (isOIden' n) ppn <> parens (sepBy comma pp1) $+$ ppann $+$ ppo)
    pp (AxiomType isLeak _ args ann _) = do
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            returnS $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        returnS $ ppLeak (lkgBool isLeak) (text "axiom" <+> parens (sepBy comma pp1) $+$ ppann)
    pp (LemmaType isLeak _ n args ann stmts _) = do
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            returnS $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        returnS $ ppLeak (lkgBool isLeak) (text "lemma" <+> ppn <+> parens (sepBy comma pp1) $+$ ppann $+$ ppo)
        
instance (DebugM m,Monad m) => PP m BaseType where
    pp (TyPrim p) = pp p
    pp (TApp n ts d) = do
        ppn <- pp n
        ppts <- mapM (ppVariadicArg pp) ts
        ppd <- pp d
        returnS $ parens (ppn <> abrackets (sepBy comma $ ppts) <+> ppd)
    pp (MSet t) = do
        ppt <- pp t
        returnS $ text "multiset" <> braces ppt
    pp (Set t) = do
        ppt <- pp t
        returnS $ text "set" <> braces ppt
    pp (BVar v c) = do
        ppv <- pp v
        ppc <- pp c
        returnS $ ppv <+> ppc
instance (DebugM m,Monad m) => PP m ComplexType where
    pp Void = returnS $ text "void"
    pp (CType s t d) = do
        pps <- pp s
        ppt <- pp t
        ppd <- pp d
        returnS $ pps <+> ppt <> brackets (brackets ppd)
    pp (CVar v b) = pp v
instance (Monad m) => PP m SysType where
    pp t@(SysPush {}) = returnS $ text (show t)
    pp t@(SysRet {}) =  returnS $ text (show t)
    pp t@(SysRef {}) =  returnS $ text (show t)
    pp t@(SysCRef {}) = returnS $ text (show t)

instance (DebugM m,Monad m) => PP m Type where
    pp t@(NoType msg) = returnS $ text "no type" <+> text msg
    pp (VAType t sz) = do
        ppt <- pp t
        ppsz <- pp sz
        returnS $ parens $ ppt <> text "..." <> nonemptyParens ppsz
    pp t@(TType b) = returnS $ text "complex type" <+> ppid b
    pp t@(BType c) = returnS $ text "base type" <+> ppid c
    pp t@DType = returnS $ text "declaration type"
    pp t@(KindT k) = pp k
    pp t@(KType b) = returnS $ text "kind type" <+> ppid b
    pp t@(StmtType {}) = returnS $ text (show t)
    pp (BaseT b) = pp b
    pp (ComplexT c) = pp c
    pp (SecT s) = pp s
    pp (DecT d) = pp d
    pp (IDecT d) = pp d
    pp (DecCtxT d) = pp d
    pp (TCstrT d) = pp d
    pp (SysT s) = pp s
    pp (IdxT e) = pp e
    pp (VArrayT a) = pp a
    pp (WhileT rs ws) = do
        prs <- pp rs
        pws <- pp ws
        returnS $ prs <+> pws
--    pp (CondType t c) = ppConstrained pp (Constrained t $ Just c)

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
    | ExprC TypeClass -- type of regular expressions (also for index expressions)
    | TypeC -- regular type
    | SysC -- system call parameters
    | DecC -- type of declarations
    | VArrayC TypeClass -- array type
  deriving (Read,Show,Data,Typeable,Eq,Ord)

instance (Monad m) => PP m TypeClass where
    pp KindStarC = returnS $ text "kind star"
    pp (VArrayStarC t) = liftM (text "array star of" <+>) (pp t)
    pp KindC = returnS $ text "kind"
    pp DomainC = returnS $ text "domain"
    pp TypeStarC = returnS $ text "type star"
    pp (ExprC c) = liftM (text "index expression" <+>) (pp c)
    pp TypeC = returnS $ text "complex type"
    pp SysC = returnS $ text "system call parameter"
    pp DecC = returnS $ text "declaration"
    pp (VArrayC t) = liftM (text "array" <+>) (pp t)

typeClass :: String -> Type -> TypeClass
--typeClass msg (CondType t _) = typeClass msg t
typeClass msg (TType b) = TypeStarC
typeClass msg (VAType b _) = VArrayStarC (typeClass msg b)
typeClass msg (BType c) = TypeStarC
typeClass msg (KType _) = KindStarC
typeClass msg (KindT _) = KindC
typeClass msg (SecT _) = DomainC
--typeClass msg (KindT _) = KindC
typeClass msg (DecT _) = DecC
typeClass msg (SysT _) = SysC
typeClass msg (IdxT e) = ExprC $ typeClass msg $ loc e
typeClass msg (VArrayT (VAVal ts b)) = VArrayC (typeClass msg b)
typeClass msg (VArrayT (VAVar v b sz)) = VArrayC (typeClass msg b)
typeClass msg (ComplexT _) = TypeC
typeClass msg (BaseT _) = TypeC
typeClass msg t = error $ msg ++ ": no typeclass for " ++ show t

isStruct :: DecType -> Bool
isStruct (DecType _ _ _ _ _ _ (StructType {})) = True
isStruct _ = False

isAxiom :: DecType -> Bool
isAxiom (DecType _ _ _ _ _ _ (AxiomType {})) = True
isAxiom _ = False

isStructTemplate :: Type -> Bool
isStructTemplate (DecT (DecType _ _ _ _ _ _ (StructType {}))) = True
isStructTemplate _ = False

isVoid :: ComplexType -> Bool
isVoid Void = True
isVoid _ = False

isNotVoid :: ComplexType -> Bool
isNotVoid Void = False
isNotVoid (CType {}) = True
isNotVoid (CVar _ b) = b

isCVar (CVar v _) = True
isCVar _ = False

isCType (CType {}) = True
isCType _ = False

baseCType (CType s b _) = b
baseCType x = error $ "baseCType: " ++ show x

secCType (CType s b _) = s
secCType x = error $ "secCType: " ++ show x

dimCType (CType s b d) = d
dimCType x = error $ "baseCType: " ++ show x

unComplexT (ComplexT ct) = ct

isVoidType :: Type -> Bool
isVoidType (ComplexT Void) = True
isVoidType _ = False

isBoolType :: Type -> Bool
isBoolType (BaseT b) = isBoolBaseType b
isBoolType _ = False

isBoolBaseType :: BaseType -> Bool
isBoolBaseType (TyPrim (DatatypeBool _)) = True
isBoolBaseType _ = False

isUint8BaseType :: BaseType -> Bool
isUint8BaseType (TyPrim (DatatypeUint8 _)) = True
isUint8BaseType _ = False

isUint16BaseType :: BaseType -> Bool
isUint16BaseType (TyPrim (DatatypeUint16 _)) = True
isUint16BaseType _ = False

isUint32BaseType :: BaseType -> Bool
isUint32BaseType (TyPrim (DatatypeUint32 _)) = True
isUint32BaseType _ = False

isUint64BaseType :: BaseType -> Bool
isUint64BaseType (TyPrim (DatatypeUint64 _)) = True
isUint64BaseType _ = False

isFloat32BaseType :: BaseType -> Bool
isFloat32BaseType (TyPrim (DatatypeFloat32 _)) = True
isFloat32BaseType _ = False

isFloat64BaseType :: BaseType -> Bool
isFloat64BaseType (TyPrim (DatatypeFloat64 _)) = True
isFloat64BaseType _ = False

isIntType :: Type -> Bool
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

isPrimType :: Type -> Bool
isPrimType (BaseT b) = isPrimBaseType b
isPrimType _ = False

isPrimBaseType :: BaseType -> Bool
isPrimBaseType (TyPrim {}) = True
isPrimBaseType _ = False

instance (Monad m) => PP m StmtClass where
    pp = returnS . text . show

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m StmtClass where
    traverseVars f c = returnS c
  
instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m SecType where
    traverseVars f Public = returnS Public
    traverseVars f (Private d k) = returnS $ Private d k
    traverseVars f (SVar v k) = do
        VIden v' <- f (VIden v::GIdentifier)
        k' <- inRHS $ f k
        returnS $ SVar v' k'
    substL (SVar v _) = returnS $ Just $ VIden v
    substL e = returnS $ Nothing

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m [TCstr] where
    traverseVars f xs = mapM f xs
    
instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m [TcCstr] where
    traverseVars f xs = mapM f xs

instance (DebugM m) => PP m [TCstr] where
    pp xs = do
        pxs <- mapM pp xs
        returnS $ brackets (sepBy comma pxs)
    
instance (DebugM m) => PP m [TcCstr] where
    pp xs = do
        pxs <- mapM pp xs
        returnS $ brackets (sepBy comma pxs)

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m DecClass where
    traverseVars f (DecClass x i y z) = do
        x' <- f x
        i' <- f i
        y' <- traverseDecClassVars f y
        z' <- traverseDecClassVars f z
        returnS (DecClass x' i' y' z')

instance (DebugM m,Monad m) => PP m DecClass where
    pp (DecClass False inline r w) = do
        ppr <- pp r
        ppw <- pp w
        returnS $ ppInline inline <+> ppr <+> ppw
    pp (DecClass True inline r w) = do
        ppr <- pp r
        ppw <- pp w
        returnS $ text "annotation" <+> ppInline inline <+> ppr <+> ppw

type DecClassVars = (Map VarIdentifier (Type,Bool),Bool)

emptyDecClassVars :: DecClassVars
emptyDecClassVars = (Map.empty,False)

isGlobalDecClassVars :: DecClassVars -> Bool
isGlobalDecClassVars (xs,b) = b || not (Map.null $ Map.filter snd xs)

traverseDecClassVars :: (DebugM m,GenVar VarIdentifier m,MonadIO m) => (forall b . Vars GIdentifier m b => b -> VarsM GIdentifier m b) -> DecClassVars -> VarsM GIdentifier m DecClassVars
traverseDecClassVars f (y,b) = do
    y' <- liftM (Map.fromList . map (mapFst unVIden) . Map.toList) $ f $ Map.fromList . map (mapFst VIden) $ Map.toList y
    b' <- f b
    returnS (y',b')

ppInline True = text "inline"
ppInline False = text "noinline"

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m [GIdentifier] where
    traverseVars = mapM
    
instance (DebugM m) => PP m [GIdentifier] where
    pp = liftM (sepBy comma) . mapM pp

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m [Var] where
    traverseVars = mapM
    
instance (DebugM m) => PP m [Var] where
    pp = liftM (sepBy comma) . mapM ppVarTy

instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m DecTypeK where
    traverseVars f (DecTypeInst i isRec) = do
        i' <- f i
        isRec' <- f isRec
        returnS $ DecTypeInst i' isRec'
    traverseVars f (DecTypeOri isRec) = do
        isRec' <- f isRec
        returnS $ DecTypeOri isRec'
    traverseVars f (DecTypeCtx) = do
        returnS $ DecTypeCtx

instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m DecType where
    traverseVars f (DecType tid isRec vs hctx bctx spes t) = do
        isRec' <- f isRec
        varsBlock $ do
            vs' <- inLHS False $ mapM f vs
            hctx' <- f hctx
            bctx' <- f bctx
            spes' <- mapM f spes
            t' <- f t
            returnS $ DecType tid isRec' vs' hctx' bctx' spes' t'
    traverseVars f (DVar v) = do
        VIden v' <- f (VIden v::GIdentifier)
        returnS $ DVar v'
    substL (DVar v) = returnS $ Just $ VIden v
    substL _ = returnS Nothing

instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m InnerDecType where
    traverseVars f (ProcType p n vs t ann stmts c) = varsBlock $ do
        n' <- f n
        vs' <- inLHS False $ mapM f vs
        t' <- f t
        ann' <- mapM f ann
        stmts' <- f stmts
        c' <- f c
        returnS $ ProcType p n' vs' t' ann' stmts' c'
    traverseVars f (LemmaType isLeak p n vs ann stmts c) = varsBlock $ do
        n' <- f n
        vs' <- inLHS False $ mapM f vs
        ann' <- mapM f ann
        stmts' <- f stmts
        c' <- f c
        returnS $ LemmaType isLeak p n' vs' ann' stmts' c'
    traverseVars f (FunType isLeak p n vs t ann stmts c) = varsBlock $ do
        n' <- f n
        vs' <- inLHS False $ mapM f vs
        t' <- f t
        ann' <- mapM f ann
        stmts' <- f stmts
        c' <- f c
        returnS $ FunType isLeak p n' vs' t' ann' stmts' c'
    traverseVars f (AxiomType isLeak p ps ann c) = varsBlock $ do
        ps' <- inLHS False $ mapM f ps
        ann' <- mapM f ann
        c' <- f c
        returnS $ AxiomType isLeak p ps' ann' c'
    traverseVars f (StructType p n as cl) = varsBlock $ do
        n' <- f n
        as' <- inLHS True $ mapM f as
        cl' <- f cl
        returnS $ StructType p n' as' cl'
    
instance (DebugM m,MonadIO m,GenVar VarIdentifier m) => Vars GIdentifier m BaseType where
    traverseVars f (TyPrim p) = do
        p' <- f p
        returnS $ TyPrim p'
    traverseVars f (MSet t) = do
        t' <- f t
        returnS $ MSet t'
    traverseVars f (Set t) = do
        t' <- f t
        returnS $ Set t'
    traverseVars f (TApp n ts d) = do
        n' <- f n
        ts' <- mapM f ts
        d' <- f d
        returnS $ TApp n' ts' d'
    traverseVars f (BVar v c) = do
        VIden v' <- f (VIden v::GIdentifier)
        c' <- inRHS $ f c
        returnS $ BVar v' c'
    substL (BVar v _) = returnS $ Just $ VIden v
    substL e = returnS Nothing
 
instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m VArrayType where
    traverseVars f (VAVal ts b) = do
        ts' <- f ts
        b' <- f b
        returnS $ VAVal ts' b'
    traverseVars f (VAVar v b sz) = do
        VIden v' <- f (VIden v::GIdentifier)
        b' <- inRHS $ f b
        sz' <- inRHS $ f sz
        returnS $ VAVar v' b' sz'
    substL (VAVar v _ _) = returnS $ Just $ VIden v
    substL e = returnS Nothing
 
instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m ComplexType where
    traverseVars f (CType s t d) = do
        s' <- f s
        t' <- f t
        d' <- f d
        returnS $ CType s' t' d' 
    traverseVars f (CVar v b) = do
        VIden v' <- f (VIden v::GIdentifier)
        b' <- inRHS $ f b
        returnS $ CVar v' b'
    traverseVars f Void = returnS Void
    substL (CVar v b) = returnS $ Just $ VIden v
    substL e = returnS Nothing

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m SysType where
    traverseVars f (SysPush t) = do
        t' <- f t
        returnS $ SysPush t'
    traverseVars f (SysRet t) = do
        t' <- f t
        returnS $ SysRet t'
    traverseVars f (SysRef t) = do
        t' <- f t
        returnS $ SysRef t'
    traverseVars f (SysCRef t) = do
        t' <- f t
        returnS $ SysCRef t'

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m KindType where
    traverseVars f PublicK = returnS PublicK
    traverseVars f (PrivateK k) = returnS $ PrivateK k
    traverseVars f (KVar k b) = do
        VIden k' <- f (VIden k::GIdentifier)
        b' <- f b
        returnS $ KVar k' b'
    substL (KVar v _) = returnS $ Just $ VIden v
    substL e = returnS Nothing

instance (DebugM m) => PP m KindType where
    pp PublicK = returnS $ text "public"
    pp (PrivateK k) = pp k
    pp (KVar k c) = do
        ppk <- pp k
        ppc <- pp c
        returnS $ ppk <+> ppc

type Attr = Attribute GIdentifier Type

instance (DebugM m,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m Type where
    traverseVars f (NoType x) = returnS (NoType x)
    traverseVars f (TType b) = returnS (TType b)
    traverseVars f (VAType t sz) = do
        t' <- f t
        sz' <- f sz
        returnS $ VAType t' sz'
    traverseVars f DType = returnS DType
    traverseVars f (BType c) = do
        c' <- f c
        returnS $ BType c'
    traverseVars f (KType b) = do
        b' <- f b
        returnS $ KType b'
    traverseVars f (KindT s) = do
        s' <- f s
        returnS $ KindT s'
    traverseVars f (IDecT s) = do
        s' <- f s
        returnS $ IDecT s'
    traverseVars f (DecCtxT s) = do
        s' <- f s
        returnS $ DecCtxT s'
    traverseVars f (TCstrT s) = do
        s' <- f s
        returnS $ TCstrT s'
    traverseVars f (StmtType s) = do
        s' <- mapSetM f s
        returnS (StmtType s')
    traverseVars f (ComplexT c) = do
        c' <- f c
        returnS $ ComplexT c'
    traverseVars f (BaseT c) = do
        c' <- f c
        returnS $ BaseT c'
    traverseVars f (SecT c) = do
        c' <- f c
        returnS $ SecT c'
    traverseVars f (DecT c) = do
        c' <- f c
        returnS $ DecT c'
    traverseVars f (SysT c) = do
        c' <- f c
        returnS $ SysT c'
    traverseVars f (IdxT c) = do
        c' <- f c
        returnS $ IdxT c'
    traverseVars f (VArrayT a) = do
        a' <- f a
        returnS $ VArrayT a'
    traverseVars f (WhileT x y) = do
        x' <- traverseDecClassVars f x
        y' <- traverseDecClassVars f y
        returnS $ WhileT x' y'
--    traverseVars f (CondType t c) = do
--        t' <- f t
--        c' <- f c
--        returnS $ CondType t' c'
    --substL (BaseT (BVar v)) = returnS $ Just v
    --substL (SecT (SVar v _)) = returnS $ Just v
    --substL (ComplexT (CVar v)) = returnS $ Just v
    --substL (DecT (DVar v)) = returnS $ Just v
    --substL (IdxT (RVariablePExpr _ v)) = returnS $ Just $ varNameId v
    --substL (VArrayT (VAVar v _ _)) = returnS $ Just v
    substL e = returnS Nothing

data DecClass
    -- A procedure
    = DecClass
        Bool -- is an annotation
        Bool -- perform inlining
        DecClassVars -- read variables (isglobal)
        DecClassVars -- written variables (isglobal)
  deriving (Show,Data,Typeable,Eq,Ord,Generic)
instance Binary DecClass
instance Hashable DecClass

decClassReads :: DecClass -> DecClassVars
decClassReads (DecClass _ _ rs _) = rs

decClassWrites :: DecClass -> DecClassVars
decClassWrites (DecClass _ _ _ ws) = ws

addDecClassVars :: DecClassVars -> DecClassVars -> DecClass -> DecClass
addDecClassVars r2 w2 (DecClass isAnn isInline r1 w1) = DecClass isAnn isInline (joinVs r1 r2) (joinVs w1 w2)
      where
      --joinVs (Left b) (Right vs) = if Map.null (Map.filter snd vs) then Left b else Right vs
      --joinVs (Right vs) (Left b) = if Map.null (Map.filter snd vs) then Left b else Right vs
      --joinVs (Left b1) (Left b2) = Left $ b1 || b1
      joinVs (vs1,b1) (vs2,b2) = (Map.unionWith add vs1 vs2,b1 || b2)
          where add (x1,y1) (x2,y2) = (x1,y1 || y2)

data StmtClass
    -- | The execution of the statement may end because of reaching a returnS statement
    = StmtReturn
    -- | The execution of the statement may end because of reaching a break statement
    | StmtBreak
    -- | The execution of the statement may end because of reaching a continue statement
    | StmtContinue
    -- | The execution of the statement may end without reaching a returnS, break or continue statement
    | StmtFallthru Type
  deriving (Show,Data,Typeable,Eq,Ord,Generic) 
instance Binary StmtClass
instance Hashable StmtClass

isLoopStmtClass :: StmtClass -> Bool
isLoopStmtClass c = List.elem c [StmtBreak,StmtContinue]

isLoopBreakStmtClass :: StmtClass -> Bool
isLoopBreakStmtClass StmtBreak = True
isLoopBreakStmtClass (StmtReturn) = True
isLoopBreakStmtClass _ = False

isIterationStmtClass :: StmtClass -> Bool
isIterationStmtClass StmtContinue = True
isIterationStmtClass (StmtFallthru _) = True
isIterationStmtClass c = False

hasStmtFallthru :: Set StmtClass -> Bool
hasStmtFallthru cs = not $ Set.null $ Set.filter isStmtFallthru cs

isStmtFallthru :: StmtClass -> Bool
isStmtFallthru (StmtFallthru _) = True
isStmtFallthru c = False

data Typed a = Typed a Type
  deriving (Show,Data,Typeable,Functor,Eq,Ord,Generic)
instance Binary a => Binary (Typed a)
instance Hashable a => Hashable (Typed a)

instance (DebugM m,PP m a) => PP m (Typed a) where
    pp = pp . typed

instance (DebugM m,GenVar VarIdentifier m,MonadIO m,Vars GIdentifier m a) => Vars GIdentifier m (Typed a) where
    traverseVars f (Typed a t) = do
        a' <- f a
        t' <- inRHS $ f t
        returnS $ Typed a' t'

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
isPublicType (BaseT b) = True
isPublicType (ComplexT (CType Public _ _)) = True
isPublicType _ = False

isPublicSecType :: SecType -> Bool
isPublicSecType Public = True
isPublicSecType _ = False

data ModuleTyVarId = ModuleTyVarId
    { modTyName :: (Maybe (Identifier,TyVarId))
    , modTyId :: TyVarId
    }
  deriving (Eq,Ord,Data,Generic,Show)
instance Monad m => PP m ModuleTyVarId where
    pp (ModuleTyVarId name i) = case name of
        Just (m,blk) -> do
            ppm <- pp m
            ppblk <- pp blk
            ppi <- pp i
            returnS $ ppm <> char '.' <> ppblk <> char '.' <> ppi
        Nothing -> do
            ppi <- pp i
            returnS $ text "BUILTIN" <> char '.' <> ppi
instance Binary ModuleTyVarId
instance Hashable ModuleTyVarId

hashModuleTyVarId :: ModuleTyVarId -> Int
hashModuleTyVarId = hashWithSalt 0 . modTyId

instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m ModuleTyVarId where
    traverseVars f x = returnS x

decTypeReturn :: DecType -> Maybe Type
decTypeReturn (DecType _ _ _ _ _ _ d) = iDecTypeReturn d

iDecTypeReturn :: InnerDecType -> Maybe Type
iDecTypeReturn (ProcType _ _ _ ret _ _ _) = Just ret
iDecTypeReturn (FunType _ _ _ _ ret _ _ _) = Just ret
iDecTypeReturn (StructType {}) = Nothing
iDecTypeReturn (AxiomType {}) = Nothing
iDecTypeReturn (LemmaType {}) = Just $ ComplexT Void

decTypeK :: DecType -> DecTypeK
decTypeK (DecType i isRec _ _ _ _ _) = isRec

decTypeTyVarId :: DecType -> Maybe ModuleTyVarId
decTypeTyVarId (DecType i _ _ _ _ _ _) = Just i
decTypeTyVarId (DVar _) = Nothing

typeTyVarId :: Type -> Maybe ModuleTyVarId
typeTyVarId (DecT dec) = decTypeTyVarId dec
typeTyVarId t = error $ "typeTyVarId" ++ show t

instance Location Type where
    locpos = const noloc
    noloc = NoType "noloc"
    updpos t p = t

instance Location a => Location (Constrained a) where
    locpos = locpos . unConstrained
    noloc = Constrained noloc Nothing
    updpos t p = t

exprTypes :: (Data iden,Data a) => Expression iden a -> [Type]
exprTypes = everything (++) (mkQ [] aux)
    where
    aux :: Type -> [Type]
    aux = (:[])

setBase b (CType s t d) = CType s b d

-- Left = type template
-- Right = procedure overload
type TIdentifier = GIdentifier' Type --Either SIdentifier PIdentifier

type SIdentifier = GIdentifier --TypeName VarIdentifier ()

--ppStructAtt :: Attr -> Doc
--ppStructAtt (Attribute _ t n szs) = pp t <+> pp n

ppTpltArg :: (DebugM m) => Constrained Var -> m Doc
ppTpltArg = ppConstrained ppTpltArg'
    where
    ppTpltArg' :: (DebugM m) => Var -> m Doc
    ppTpltArg' (VarName (BType c) v) = do
        ppv <- pp v
        returnS $ maybe PP.empty ppDataClass c <+> text "type" <+> ppv
    ppTpltArg' (VarName (KType isPriv) k) = do
        ppk <- pp k
        returnS $ maybe PP.empty ppKindClass isPriv <+> text "kind" <+> ppk
    ppTpltArg' (VarName (KindT k) v) = do
        ppv <- pp v
        ppk <- pp k
        returnS $ text "domain" <+> ppv <+> char ':' <+> ppk
    ppTpltArg' (VarName t v) | isIntType t = liftM (text "dim" <+>) (pp v)
    ppTpltArg' (VarName (VAType b sz) v) | isIntType b = liftM (text "dim..." <+>) (pp v)
    ppTpltArg' (VarName (VAType (BType c) sz) v) = do
        ppv <- pp v
        returnS $ maybe PP.empty ppDataClass c <+> text "type..." <+> ppv
    ppTpltArg' (VarName (VAType (KType isPriv) sz) v) = do
        ppv <- pp v
        returnS $ maybe PP.empty ppKindClass isPriv <+> text "kind..." <+> ppv
    ppTpltArg' (VarName (VAType (KindT k) sz) v) = do
        ppv <- pp v
        ppk <- pp k
        returnS $ text "domain..." <+> ppv <+> ppk
    ppTpltArg' v = do
        ppv <- pp v
        ppl <- pp (loc v)
        error $ "ppTpltArg: " ++ show ppv ++ " " ++ show ppl
    
ppTSubsts :: (DebugM m) => TSubsts -> m Doc
ppTSubsts xs = liftM vcat $ mapM ppSub $ Map.toList (unTSubsts xs)
    where
    ppSub (k,IdxT e) = do
        ppk <- pp k
        ppe <- ppExprTy e
        returnS $ ppk <+> char '=' <+> ppe
    ppSub (k,t) = do
        ppk <- pp k
        ppt <- pp t
        returnS $ ppk <+> char '=' <+> ppt

ppArrayRanges :: (DebugM m) => [ArrayProj] -> m Doc
ppArrayRanges xs = liftM (sepBy comma) (mapM pp xs)

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
defCType t = CType Public t (indexExpr 0)

instance Hashable VarIdentifier where
    hashWithSalt i v = hashWithSalt (maybe i ((i+) . hashTyVarId) $ varIdUniq v) (varIdBase v)

type Prim = PrimitiveDatatype ()

removeOrWarn :: SecrecError -> SecrecError
removeOrWarn = everywhere (mkT f) where
    f (OrWarn err) = err
    f err = err

varIdxT :: Var -> Type
varIdxT v = IdxT $ varExpr v

askOpts :: Monad m => TcM m Options
askOpts = TcM $ lift Reader.ask

localOpts :: Monad m => (Options -> Options) -> TcM m a -> TcM m a
localOpts f (TcM m) = TcM $ RWS.mapRWST (SecrecM . Reader.local f . unSecrecM) m

withoutImplicitClassify :: Monad m => TcM m a -> TcM m a
withoutImplicitClassify m = localOpts (\opts -> opts { implicitCoercions = OffC }) m

instance MonadIO m => GenVar VarIdentifier (TcM m) where
    genVar v = freshVarId (varIdBase v) (varIdPretty v)
    mkVar = returnS . mkVarId

instance (GenVar VarIdentifier m) => GenVar (GIdentifier' t) m where
    genVar (VIden v) = liftM VIden $ genVar v
    genVar v = returnS v
    mkVar = liftM VIden . mkVar

--instance MonadIO m => GenVar VarIdentifier (SecrecM m) where
--    genVar v = freshVarIO v

instance (DebugM m,Location t,Vars GIdentifier m t,GenVar VarIdentifier m,MonadIO m) => Vars GIdentifier m (GIdentifier' t) where
    traverseVars f (OIden o) = do
        o' <- f o
        isLHS <- getLHS
        if isJust isLHS then addBV funit (OIden o') else addFV funit (OIden o')
    traverseVars f n = do
        isLHS <- getLHS
        if isJust isLHS then addBV funit n else addFV funit n
    substL (OIden v) = returnS $ Just $ OIden $ funit v
    substL (VIden v) = returnS $ Just $ VIden v
    substL (PIden v) = returnS $ Just $ PIden v
    substL (TIden v) = returnS $ Just $ TIden v
    substL v = returnS Nothing

instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m VarIdentifier where
    traverseVars f n = do
        isLHS <- getLHS
        if isJust isLHS then addBV id n else addFV id n
    substL v = returnS $ Just v

-- filter the constraints that depend on a set of variables
varsCstrGraph :: (VarsGTcM m) => Set VarIdentifier -> GCstrGraph -> TcM m GCstrGraph
varsCstrGraph vs gr = labnfilterM aux (Graph.trc gr)
    where
    aux (i,x) = do
        xvs <- usedVs (kCstr $ unLoc x)
        if Set.null (vs `Set.intersection` xvs)
            then returnS False
            else returnS True

usedVs :: (Vars GIdentifier (TcM m) a) => a -> TcM m (Set VarIdentifier)
usedVs x = do
    (fs,bs) <- uvs x
    returnS $ Set.union (videns $ Map.keysSet fs) (videns $ Map.keysSet bs)

writtenVs :: (Vars GIdentifier (TcM m) a) => a -> TcM m (Set VarIdentifier)
writtenVs x = do
    (fs,bs) <- uvs x
    returnS $ (videns $ Map.keysSet bs)


compoundStmts :: Location loc => loc -> [Statement iden (Typed loc)] -> [Statement iden (Typed loc)]
compoundStmts l = maybeToList . compoundStmtMb l

compoundStmtMb :: Location loc => loc -> [Statement iden (Typed loc)] -> Maybe (Statement iden (Typed loc))
compoundStmtMb l ss = if null ss then Nothing else Just (compoundStmt l ss)

compoundStmt :: Location loc => loc -> [Statement iden (Typed loc)] -> Statement iden (Typed loc)
compoundStmt l ss = CompoundStatement (Typed l t) ss
    where
    t = unStmts $ map (typed . loc) ss
    unStmts [] = StmtType Set.empty
    unStmts (StmtType x':xs) = do
        case unStmts xs of
            (StmtType xs') -> StmtType $ Set.union x' xs'
            t -> NoType "compoundStmtMb"
    unStmts (x:xs) = NoType "compoundStmtMb"

annStmts :: Location loc => loc -> [StatementAnnotation iden (Typed loc)] -> [Statement iden (Typed loc)]
annStmts l = maybeToList . annStmtMb l

annStmtMb :: Location loc => loc -> [StatementAnnotation iden (Typed loc)] -> Maybe (Statement iden (Typed loc))
annStmtMb l ss = if null ss then Nothing else Just (annStmt l ss)

annStmt :: Location loc => loc -> [StatementAnnotation iden (Typed loc)] -> Statement iden (Typed loc)
annStmt l ss = AnnStatement (Typed l t) ss
    where
    t = unStmts $ map (typed . loc) ss
    unStmts [] = StmtType Set.empty
    unStmts (StmtType x':xs) = do
        case unStmts xs of
            (StmtType xs') -> StmtType $ Set.union x' xs'
            t -> NoType "compoundStmtMb"
    unStmts (x:xs) = NoType "compoundStmtMb"

assertStmtAnn isLeak e = AnnStatement ast [AssertAnn ast isLeak e]
    where
    ast = StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void
assertStmt e = AssertStatement ast e
    where
    ast = StmtType $ Set.singleton $ StmtFallthru $ ComplexT Void
    
unDecT (DecT x) = x
unDecT t = error $ "unDecT: " ++ show t
unKindT (KindT x) = x
unKindT t = error $ "unKindT: " ++ show t
unSecT (SecT x) = x
unSecT t = error $ "unSecT: " ++ show t

isDomain k = k == KindC || k == VArrayC KindC
isKind k = k == KindStarC || k == VArrayC KindStarC
isType k = k == TypeStarC || k == VArrayC TypeStarC
isVariable k = k == TypeC || k == VArrayStarC TypeC

debugTc :: Monad m => TcM m () -> TcM m ()
{-# INLINE debugTc #-}
debugTc m = do
    opts <- askOpts
    if debug opts then m else returnS ()

