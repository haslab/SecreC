{-# LANGUAGE TemplateHaskell, MagicHash, DeriveGeneric, Rank2Types, UndecidableInstances, DeriveFoldable, DeriveTraversable, FlexibleContexts, ConstraintKinds, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

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
import Data.Graph.Inductive.Query as Graph hiding (mapSnd)
import Data.Text.Unsafe

import GHC.Generics (Generic)
import GHC.Base hiding (mapM)
import GHC.Num

import Control.Applicative
import Control.Monad.State (State(..),StateT(..),MonadState(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (Reader(..),ReaderT(..),MonadReader(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.Writer (Writer(..),WriterT(..),MonadWriter(..))
import qualified Control.Monad.Writer as Writer hiding ((<>))
import Control.Monad.Trans.RWS (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS as RWS
import Control.Monad.Except
import Control.Monad.Trans.Control
import Control.Monad.Identity

import Safe

import Unsafe.Coerce

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as PP

import qualified Data.HashTable.Weak.IO as WeakHash

import System.IO.Unsafe
import qualified System.Mem.Weak.Map as WeakMap
import System.Mem.Weak.Exts as Weak
import System.Exit
import System.IO
import System.Posix.Types
import System.Posix.Files
import System.FilePath.Posix
import System.IO.Error

import Debug.Trace

data SolveMode = SolveMode { solveFail :: SolveFail, solveScope :: SolveScope }
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

data IOCstr = IOCstr
    { kCstr :: TCstr
    , kStatus :: !(IdRef ModuleTyVarId TCstrStatus)
    }
  deriving (Data,Typeable,Show)

instance Hashable IOCstr where
    hashWithSalt i k = hashWithSalt i (kCstr k)
  
instance Eq IOCstr where
    k1 == k2 = kStatus k1 == kStatus k2
instance Ord IOCstr where
    compare k1 k2 = compare (kStatus k1) (kStatus k2)

instance PP m VarIdentifier => PP m IOCstr where
    pp k = do
        pp1 <- pp (ioCstrId k)
        pp2 <- pp (kCstr k)
        return $ pp1 <+> char '=' <+> pp2

data TCstrStatus
    = Unevaluated -- has never been evaluated
    | Evaluated -- has been evaluated
        TDict -- resolved dictionary (variables bindings and recursive constraints)
        ShowOrdDyn -- result value
    | Erroneous -- has failed
        SecrecError -- failure error
  deriving (Data,Typeable,Show,Generic)

instance Hashable TCstrStatus

data Scope = GlobalScope | LocalScope
  deriving (Show,Read,Data,Typeable,Generic)

instance Binary Scope
instance Hashable Scope

instance Monad m => PP m Scope where
    pp GlobalScope = return $ text "global"
    pp LocalScope = return $ text "local"

{-# NOINLINE globalEnv #-}
globalEnv :: IORef GlobalEnv
globalEnv = unsafePerformIO (newGlobalEnv >>= newIORef)

newGlobalEnv :: IO GlobalEnv
newGlobalEnv = do
    m <- WeakHash.newSized (1024*4)
    iom <- WeakHash.newSized (1024*4)
    cstrs <- WeakHash.newSized 2048
    return $ GlobalEnv m iom cstrs

resetGlobalEnv :: IO ()
resetGlobalEnv = do
    g <- readIORef globalEnv
    deps <- WeakHash.newSized 1024
    iodeps <- WeakHash.newSized 512
    cstrs <- WeakHash.newSized 2048
    writeIORef globalEnv $ g { tDeps = deps, ioDeps = iodeps, gCstrs = cstrs }

orWarn :: (MonadIO m) => TcM m a -> TcM m (Maybe a)
orWarn m = (liftM Just m) `catchError` \e -> do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Map.singleton (loc e) $ Set.singleton $ ErrWarn e
--    liftIO $ putStrLn $ "warning... " ++ ppr e
    return Nothing

orWarn_ :: (MonadIO m) => TcM m a -> TcM m ()
orWarn_ m = orWarn m >> return ()

type POId = Either VarIdentifier (Op VarIdentifier ())

data GIdentifier
    = VIden VarIdentifier -- variable
    | PIden VarIdentifier -- function or procedure or lemma
    | OIden (Op VarIdentifier ()) -- operator function or procedure
    | TIden VarIdentifier -- type
  deriving (Eq,Ord,Show,Data,Typeable,Generic)
instance Hashable GIdentifier
instance Binary GIdentifier

instance PP m VarIdentifier => PP m GIdentifier where
    pp (VIden v) = pp v
    pp (PIden v) = pp v
    pp (OIden v) = pp v
    pp (TIden v) = pp v

gIdenBase :: PP m VarIdentifier => GIdentifier -> m String
gIdenBase (VIden v) = return $ varIdBase v
gIdenBase (PIden v) = return $ varIdBase v
gIdenBase (TIden v) = return $ varIdBase v
gIdenBase (OIden o) = ppr o

data GlobalEnv = GlobalEnv
    { tDeps :: WeakHash.BasicHashTable GIdentifier (WeakMap.WeakMap TyVarId IOCstr) -- IOCstr dependencies on variables
    , ioDeps :: WeakHash.BasicHashTable TyVarId (WeakMap.WeakMap TyVarId IOCstr) -- IOCstr dependencies on other IOCstrs
    , gCstrs :: WeakHash.BasicHashTable TCstr IOCstr -- hashtable of generated constraints for possbile reuse
    }

type Deps = Set LocIOCstr

getModuleCount :: (Monad m) => TcM m Int
getModuleCount = liftM (snd . moduleCount) State.get

-- global typechecking environment
data TcEnv = TcEnv {
      localVars  :: Map VarIdentifier (Bool,Bool,EntryEnv) -- ^ local variables: name |-> (isConst,isAnn,type of the variable)
    , localFrees :: Frees -- ^ free internal const variables generated during typechecking
    , localConsts :: Map Identifier VarIdentifier
    , globalDeps :: Deps -- ^ global dependencies
    , localDeps :: Deps -- ^ local dependencies
    , tDict :: [TDict] -- ^ A stack of dictionaries
    , openedCstrs :: [(IOCstr,Set VarIdentifier)] -- constraints being resolved, for dependency tracking: ordered map from constraints to bound variables
    , lineage :: Lineage -- lineage of the constraint being processed
    , moduleCount :: ((String,TyVarId),Int)
    , inTemplate :: Bool -- if typechecking inside a template, global constraints are delayed
    , decKind :: DecKind -- if typechecking inside a declaration
    , exprC :: ExprC -- type of expression
    , isLeak :: Bool -- if typechecking leakage expressions
    , decClass :: DecClass -- class when typechecking procedures
    , moduleEnv :: (ModuleTcEnv,ModuleTcEnv) -- (aggregate module environment for past modules,plus the module environment for the current module)
    }

data ExprC = ReadOnlyE | ReadWriteE | PureE
  deriving (Eq,Show,Data,Typeable,Generic)
instance Ord ExprC where
    compare x y | x == y = EQ 
    compare PureE _ = LT
    compare _ PureE = GT
    compare ReadOnlyE _ = LT
    compare _ ReadOnlyE = GT
instance Hashable ExprC
instance Binary ExprC
instance Monad m => PP m ExprC where
    pp = return . text . show

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
    pp = return . text . show

-- module typechecking environment that can be exported to an interface file
data ModuleTcEnv = ModuleTcEnv {
      globalVars :: Map VarIdentifier (Maybe Expr,(Bool,Bool,EntryEnv)) -- ^ global variables: name |-> (isConst,isAnn,type of the variable)
    , globalConsts :: Map Identifier VarIdentifier -- mapping from declared const variables to unique internal const variables: consts have to be in SSA to guarantee the typechecker's correctness
    , kinds :: Map VarIdentifier EntryEnv -- ^ defined kinds: name |-> type of the kind
    , domains :: Map VarIdentifier EntryEnv -- ^ defined domains: name |-> type of the domain
    -- a list of overloaded procedures; akin to Haskell type class operations
    -- we don't allow specialization of function templates
    , procedures :: Map POId (Map ModuleTyVarId EntryEnv) -- ^ defined procedures: name |-> procedure decl
    -- | a base template and a list of specializations; akin to Haskell type functions
    , functions :: Map POId (Map ModuleTyVarId EntryEnv)
    , lemmas :: Map VarIdentifier (Map ModuleTyVarId EntryEnv)
    , structs :: Map VarIdentifier (Map ModuleTyVarId EntryEnv) -- ^ defined structs: name |-> struct decl
    , axioms :: Map ModuleTyVarId EntryEnv -- defined axioms
    } deriving (Generic,Data,Typeable,Eq,Ord,Show)

instance Hashable ModuleTcEnv

instance Monad m => PP m ModuleTcEnv where
    pp = return . text . show

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

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m ModuleTcEnv where
    traverseVars f (ModuleTcEnv x1 x2 x3 x4 x5 x6 x7 x8 x9) = do
        x1' <- f x1
        x2' <- traverseMap return f x2
        x3' <- f x3
        x4' <- f x4
        x5' <- f x5
        x6' <- f x6
        x7' <- f x7
        x8' <- f x8
        x9' <- f x9
        return $ ModuleTcEnv x1' x2' x3' x4' x5' x6' x7' x8' x9'

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m EntryEnv where
    traverseVars f (EntryEnv x1 x2) = do
        x1' <- f x1
        x2' <- f x2
        return $ EntryEnv x1' x2'

--mergeStructs (x,y) (z,w) = (unionMb x z,Map.union y w)
unionMb Nothing y = y
unionMb x Nothing = x
unionMb (Just x) (Just y) = error "unionMb: cannot join two justs"

withExprC :: Monad m => ExprC -> TcM m a -> TcM m a
withExprC b m = do
    old <- liftM exprC State.get
    State.modify $ \env -> env { exprC = b }
    x <- m
    State.modify $ \env -> env { exprC = old }
    return x

limitExprC :: Monad m => ExprC -> TcM m a -> TcM m a
limitExprC c' m = do
    c <- getExprC
    withExprC (min c c') m

withLeak :: Monad m => Bool -> TcM m a -> TcM m a
withLeak b m = do
    old <- liftM isLeak State.get
    State.modify $ \env -> env { isLeak = b }
    x <- m
    State.modify $ \env -> env { isLeak = old }
    return x

withKind :: Monad m => DecKind -> TcM m a -> TcM m a
withKind k m = do
    old <- liftM decKind State.get
    State.modify $ \env -> env { decKind = k }
    x <- m
    State.modify $ \env -> env { decKind = old }
    return x

getExprC :: Monad m => TcM m ExprC
getExprC = liftM exprC State.get
    
getLeak :: Monad m => TcM m Bool
getLeak = liftM isLeak State.get

getLineage :: Monad m => TcM m Lineage
getLineage = State.gets lineage

getKind :: Monad m => TcM m (DecKind)
getKind = State.gets decKind

getCstrState :: Monad m => TcM m CstrState
getCstrState = do
    isAnn <- getAnn
    exprC <- getExprC
    lineage <- getLineage
    isLeak <- getLeak
    kind <- getKind
    return (isAnn,exprC,isLeak,kind,lineage)

withCstrState :: Monad m => CstrState -> TcM m a -> TcM m a
withCstrState (isAnn,exprC,isLeak,kind,lineage) m = withAnn isAnn $ withExprC exprC $ withLeak isLeak $ withKind kind $ withLineage lineage m

withLineage :: Monad m => Lineage -> TcM m a -> TcM m a
withLineage new m = do
    old <- State.gets lineage
    State.modify $ \env -> env { lineage = new }
    x <- m
    State.modify $ \env -> env { lineage = old }
    return x
    
getAnn :: Monad m => TcM m Bool
getAnn = liftM (isAnnDecClass . decClass) State.get

modifyModuleEnv :: Monad m => (ModuleTcEnv -> ModuleTcEnv) -> TcM m ()
modifyModuleEnv f = State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,f y) }

modifyModuleEnvM :: Monad m => (ModuleTcEnv -> TcM m ModuleTcEnv) -> TcM m ()
modifyModuleEnvM f = do
    y <- State.gets (snd . moduleEnv)
    y' <- f y
    State.modify $ \env -> env { moduleEnv = let (x,y) = moduleEnv env in (x,y') }

getModuleField :: (MonadIO m) => Bool -> (ModuleTcEnv -> x) -> TcM m x
getModuleField withBody f = do
    (x,y) <- State.gets moduleEnv
    z <- getRecs withBody
    let xyz = mappend x (mappend y z)
    return $ f xyz

-- get only the recursive declarations for the lineage
getRecs :: MonadIO m => Bool -> TcM m ModuleTcEnv
getRecs withBody = do
    lineage <- getLineage
--    debugTc $ liftIO $ putStrLn $ "getRecs: " ++ show (sepBy comma $ map pp lineage)
    State.gets (filterRecModuleTcEnv (Just lineage) withBody . mconcat . map tRec . tDict)

filterRecModuleTcEnv :: Maybe Lineage -> Bool -> ModuleTcEnv -> ModuleTcEnv
filterRecModuleTcEnv lineage withBody env = env
    { structs = filterRecBody lineage withBody (structs env)
    , procedures = filterRecBody lineage withBody (procedures env)
    , functions = filterRecBody lineage withBody (functions env)
    , lemmas = filterRecBody lineage withBody (lemmas env)
    }

filterRecBody :: Maybe Lineage -> Bool -> Map x (Map ModuleTyVarId EntryEnv) -> Map x (Map ModuleTyVarId EntryEnv)
filterRecBody lineage withBody xs = Map.map (Map.map remBody . filterLineage) xs
    where
    filterLineage = case lineage of
        Nothing -> id
        Just lin -> Map.filter (isLineage lin)
    remBody = if withBody then id else remEntryBody
    remEntryBody (EntryEnv l (DecT d)) = EntryEnv l $ DecT $ remDecBody d
    isLineage lin (EntryEnv l (DecT d)) = case decTypeId d of
        Nothing -> False
        Just x -> List.elem x lin

remDecBody :: DecType -> DecType
remDecBody d@(DecType i isRec ts hd hfrees bd bfrees specs b) =
    DecType i isRec ts hd hfrees bd bfrees specs (remIDecBody b)

remIDecBody :: InnerDecType -> InnerDecType
remIDecBody d@(ProcType pl n pargs pret panns body cl) = ProcType pl n pargs pret panns Nothing cl
remIDecBody d@(FunType isLeak pl n pargs pret panns body cl) = FunType isLeak pl n pargs pret panns Nothing cl
remIDecBody d@(StructType sl sid@(TypeName _ sn) atts cl) = StructType sl sid Nothing cl
remIDecBody d@(AxiomType isLeak p qs pargs cl) = AxiomType isLeak p qs pargs cl
remIDecBody d@(LemmaType isLeak pl n pargs panns body cl) = LemmaType isLeak pl n pargs panns Nothing cl

getStructs :: MonadIO m => Bool -> Bool -> Bool -> TcM m (Map VarIdentifier (Map ModuleTyVarId EntryEnv))
getStructs withBody isAnn isLeak = do
    liftM (filterAnns isAnn isLeak) $ getModuleField withBody structs
getKinds :: MonadIO m => TcM m (Map VarIdentifier EntryEnv)
getKinds = getModuleField True kinds
getGlobalVars :: MonadIO m => TcM m (Map VarIdentifier (Maybe Expr,(Bool,Bool,EntryEnv)))
getGlobalVars = getModuleField True globalVars
getGlobalConsts :: MonadIO m => TcM m (Map Identifier VarIdentifier)
getGlobalConsts = getModuleField True globalConsts
getDomains :: MonadIO m => TcM m (Map VarIdentifier EntryEnv)
getDomains = getModuleField True domains
getProcedures :: MonadIO m => Bool -> Bool -> Bool -> TcM m (Map POId (Map ModuleTyVarId EntryEnv))
getProcedures withBody isAnn isLeak = do
    liftM (filterAnns isAnn isLeak) $ getModuleField withBody procedures
getFunctions :: MonadIO m => Bool -> Bool -> Bool -> TcM m (Map POId (Map ModuleTyVarId EntryEnv))
getFunctions withBody isAnn isLeak = do
    liftM (filterAnns isAnn isLeak) $ getModuleField withBody functions
getLemmas :: MonadIO m => Bool -> Bool -> Bool -> TcM m (Map VarIdentifier (Map ModuleTyVarId EntryEnv))
getLemmas withBody isAnn isLeak = do
    liftM (filterAnns isAnn isLeak) $ getModuleField withBody lemmas
getAxioms :: MonadIO m => Bool -> Bool -> TcM m (Map ModuleTyVarId EntryEnv)
getAxioms isAnn isLeak = liftM (filterAnns1 isAnn isLeak) $ getModuleField True axioms

filterAnns :: Bool -> Bool -> Map x (Map y EntryEnv) -> Map x (Map y EntryEnv)
filterAnns isAnn isLeak = Map.map (filterAnns1 isAnn isLeak)

filterAnns1 :: Bool -> Bool -> (Map y EntryEnv) -> (Map y EntryEnv)
filterAnns1 isAnn isLeak = Map.filter p
    where
    p e@(entryType -> t@(DecT d)) = (isAnnDecClass (tyDecClass t) == isAnn) && (isLeak >= isLeakDec d)

insideAnnotation :: Monad m => TcM m a -> TcM m a
insideAnnotation = withAnn True

withAnn :: Monad m => Bool -> TcM m a -> TcM m a
withAnn b m = do
    isAnn <- liftM (isAnnDecClass . decClass) State.get
    State.modify $ \env -> env { decClass = chgAnnDecClass b (decClass env) }
    x <- m
    State.modify $ \env -> env { decClass = chgAnnDecClass isAnn (decClass env) }
    return x

chgAnnDecClass :: Bool -> DecClass -> DecClass
chgAnnDecClass b (DecClass _ i r w) = DecClass b i r w

chgInlineDecClass :: Bool -> DecClass -> DecClass
chgInlineDecClass b (DecClass a _ r w) = DecClass a b r w

isAnnDecClass :: DecClass -> Bool
isAnnDecClass (DecClass b _ _ _) = b

isInlineDecClass :: DecClass -> Bool
isInlineDecClass (DecClass _ b _ _) = b

withDependencies :: Monad m => Set LocIOCstr -> TcM m a -> TcM m a
withDependencies deps m = do
    State.modify $ \env -> env { localDeps = deps `Set.union` localDeps env }
    x <- m
    State.modify $ \env -> env { localDeps = localDeps env }
    return x

type VarsId m a = Vars VarIdentifier m a
type VarsIdTcM m = (Typeable m,MonadIO m,MonadBaseControl IO m,VarsId (TcM m) Position,VarsId (TcM Symbolic) Position)

emptyTcEnv :: TcEnv
emptyTcEnv = TcEnv
    { 
    localVars = Map.empty
    , localFrees = Map.empty
    , globalDeps = Set.empty
    , localDeps = Set.empty
    , tDict = []
    , openedCstrs = []
    , lineage = []
    , moduleCount = (("main",TyVarId 0),1)
    , inTemplate = False
    , decKind = FKind
    , exprC = ReadOnlyE
    , isLeak = False
    , localConsts = Map.empty
    , decClass = mempty
    , moduleEnv = (mempty,mempty)
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
   
instance PP m VarIdentifier => PP m EntryEnv where
    pp = pp . entryType
   
varNameToType :: Var -> Type
varNameToType (VarName (KType b) k) = KindT $ KVar k b
varNameToType (VarName (KindT k) n) = SecT $ SVar n k
varNameToType (VarName (TType b) n) = ComplexT $ CVar n b
varNameToType (VarName BType n) = BaseT $ BVar n
varNameToType (VarName DType n) = DecT $ DVar n
varNameToType (VarName (VAType b sz) n) = VArrayT $ VAVar n b sz
varNameToType (VarName t n) | typeClass "varNameToType" t == TypeC = IdxT (RVariablePExpr t $ VarName t n)
varNameToType v = error $ "varNameToType " ++ show v

condVarNameToType :: Constrained Var -> Type
condVarNameToType (Constrained v c) = constrainedType (varNameToType v) c

typeToVarName :: Type -> Maybe Var
typeToVarName (KindT (KVar n b)) = Just $ VarName (KType b) n
typeToVarName (SecT (SVar n k)) = Just (VarName (KindT k) n)
typeToVarName (ComplexT (CVar n b)) = Just (VarName (TType b) n)
typeToVarName (BaseT (BVar n)) = Just (VarName BType n)
typeToVarName (DecT (DVar n)) = Just (VarName DType n)
typeToVarName (VArrayT (VAVar n b sz)) = Just (VarName (VAType b sz) n)
typeToVarName (IdxT (RVariablePExpr _ (VarName t n))) | typeClass "typeToVarName" t == TypeC = Just (VarName t n)
typeToVarName _ = Nothing

tyToVar :: Type -> Var
tyToVar = fromJustNote "tyToVar" . typeToVarName

typeToTypeName :: Type -> Maybe (TypeName VarIdentifier Type)
typeToTypeName t = case typeToVarName t of
    Just (VarName _ n) -> Just $ TypeName t n
    otherwise -> Nothing
    
typeToDomainName :: Type -> Maybe (DomainName VarIdentifier Type)
typeToDomainName t = case typeToVarName t of
    Just (VarName _ n) -> Just $ DomainName t n
    otherwise -> Nothing

typeToKindName :: Type -> Maybe (KindName VarIdentifier Type)
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
        return $ SecrecErrArr $ \x -> everywhere (mkT $ aux x) err
instance Hashable SecrecErrArr where
    hashWithSalt salt err = salt

newtype TcM m a = TcM { unTcM :: RWST (Int,SecrecErrArr) () (TcEnv) (SecrecM m) a }
    deriving (Functor,Applicative,Typeable,Monad,MonadIO,MonadState (TcEnv),MonadReader (Int,SecrecErrArr),MonadWriter (),MonadError SecrecError,MonadPlus,Alternative)

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
            Left err -> return $ Left err
            Right ((x,env,()),warns) -> do
                liftIO $ printWarns warns
                return $ Right ((x,env,()),mempty)

instance MonadTrans (TcM) where
    lift m = TcM $ lift $ SecrecM $ lift $ liftM (\x -> Right (x,mempty)) m

askErrorM :: Monad m => TcM m (SecrecError -> SecrecError)
askErrorM = liftM (unSecrecErrArr . snd) $ Reader.ask

askErrorM' :: Monad m => TcM m (Int,SecrecError -> SecrecError)
askErrorM' = do
    (i,SecrecErrArr f) <- Reader.ask
    return (i,f)
    
askErrorM'' :: Monad m => TcM m (Int,SecrecErrArr)
askErrorM'' = Reader.ask

newErrorM :: TcM m a -> TcM m a
newErrorM (TcM m) = TcM $ RWS.withRWST (\f s -> ((0,SecrecErrArr id),s)) m

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: Monad m => TcM m a -> TcM m a
tcBlock m = do
    r <- Reader.ask
    s <- State.get
    (x,s',w') <- TcM $ lift $ runRWST (unTcM m) r s
    Writer.tell w'
    return x
    
tcDictBlock :: Monad m => TcM m a -> TcM m a
tcDictBlock m = do
    dicts <- State.gets tDict
    x <- m
    State.modify $ \env -> env { tDict = dicts }
    return x

execTcM :: (MonadIO m) => TcM m a -> (Int,SecrecErrArr) -> TcEnv -> SecrecM m (a,TcEnv)
execTcM m arr env = do
    (x,env',()) <- RWS.runRWST (unTcM m) arr env
    return (x,env')

runTcM :: (MonadIO m) => TcM m a -> SecrecM m a
runTcM m = liftM fst $ RWS.evalRWST (unTcM m) (0,SecrecErrArr id) emptyTcEnv

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

type PIdentifier = Either VarIdentifier (Op VarIdentifier Type)

cstrScope :: VarsIdTcM m => TCstr -> TcM m SolveScope
cstrScope k = do
    isAll <- isDelayableCstr k
    if isAll
        then return SolveAll
        else if isGlobalCstr k
            then return SolveGlobal
            else return SolveLocal

-- | Does a constraint depend on global template, procedure or struct definitions?
-- I.e., can it be overloaded?
isGlobalCstr :: TCstr -> Bool
isGlobalCstr k = isCheckCstr k || isHypCstr k || everything (||) (mkQ False isGlobalTcCstr) k

isMultipleSubstsCstr :: VarsIdTcM m => TCstr -> TcM m Bool
isMultipleSubstsCstr k = everything orM (mkQ (return False) isMultipleSubstsTcCstr) k

isDelayableCstr :: VarsIdTcM m => TCstr -> TcM m Bool
isDelayableCstr k = everything orM (mkQ (return False) mk) k
    where
    mk x = do
        is1 <- isMultipleSubstsTcCstr x
        return (is1 || isResolveTcCstr x)

isMultipleSubstsTcCstr :: VarsIdTcM m => TcCstr -> TcM m Bool
isMultipleSubstsTcCstr (MultipleSubstitutions _ [k]) = return False
isMultipleSubstsTcCstr (MultipleSubstitutions ts _) = do
    xs::Set VarIdentifier <- fvsSet ts
    if Set.null xs then return False else return True
isMultipleSubstsTcCstr _ = return False

isResolveTcCstr :: TcCstr -> Bool
isResolveTcCstr (Resolve {}) = True
isResolveTcCstr _ = False

isGlobalTcCstr :: TcCstr -> Bool
isGlobalTcCstr (Resolve {}) = True
isGlobalTcCstr (TDec {}) = True
isGlobalTcCstr (PDec {}) = True
isGlobalTcCstr (SupportedPrint {}) = True
isGlobalTcCstr (MultipleSubstitutions {}) = True
isGlobalTcCstr _ = False

-- | A template constraint with a result type
data TcCstr
    = TDec -- ^ type template declaration
        Bool -- is template
        (TypeName VarIdentifier ()) -- template name
        [(Type,IsVariadic)] -- template arguments
        DecType -- resulting type
    | PDec -- ^ procedure declaration
        PIdentifier -- procedure name
        (Maybe [(Type,IsVariadic)]) -- template arguments
        [(Expr,IsVariadic)] -- procedure arguments
        Type -- return type
        DecType -- result
        Bool -- coerce arguments
        [Var] -- resulting coerced procedure arguments
    | Equals Type Type -- ^ types equal
    | Coerces -- ^ types coercible
        Expr
        Var
    | CoercesSecDimSizes
        Expr -- source expression
        Var -- target variable where to store the resulting expression
    | CoercesN -- ^ multidirectional coercion
        [(Expr,Var)]
    | CoercesNSecDimSizes
        [(Expr,Var)]
    | CoercesLit -- coerce a literal expression into a specific type
        Expr -- literal expression with the base type given at the top-level
    | Unifies -- unification
        Type Type -- ^ type unification
    | Assigns -- assignment
        Type Type
    | SupportedPrint
        [(Expr,IsVariadic)] -- ^ can call tostring on the argument type
        [Var] -- resulting coerced procedure arguments
    | ProjectStruct -- ^ struct type projection
        BaseType (AttributeName VarIdentifier ()) 
        Type -- result
    | ProjectMatrix -- ^ matrix type projection
        Type [ArrayProj]
        Type -- result
    | IsReturnStmt (Set StmtClass) -- ^ is return statement
    | MultipleSubstitutions
        [Type] -- bound variable
        [([TCstr],[TCstr],Set VarIdentifier)] -- mapping from multiple matching conditions to their dependencies and free variables
    | MatchTypeDimension
        Expr -- type dimension
        [(Expr,IsVariadic)] -- sequence of sizes
    | IsValid -- check if an index condition is valid (this is mandatory: raises an error)
        Cond -- condition
    | NotEqual -- expressions not equal
        Expr Expr
    | TypeBase Type BaseType
    | IsPublic Bool Type
    | IsPrivate Bool Type
    | ToMultiset Type ComplexType
    | Resolve Type
    | Default (Maybe [(Expr,IsVariadic)]) Expr
  deriving (Data,Typeable,Show,Eq,Ord,Generic)

instance Binary TcCstr
instance Hashable TcCstr
 
isTrivialTcCstr :: TcCstr -> Bool
isTrivialTcCstr (Equals t1 t2) = t1 == t2
isTrivialTcCstr (Coerces e v) = e == varExpr v
isTrivialTcCstr (CoercesSecDimSizes e v) = e == varExpr v
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
isTrivialCstr (TcK c _) = isTrivialTcCstr c
isTrivialCstr (DelayedK c _) = isTrivialCstr c
isTrivialCstr (CheckK c _) = isTrivialCheckCstr c
isTrivialCstr (HypK c _) = isTrivialHypCstr c

type Var = VarName VarIdentifier Type
type Expr = Expression VarIdentifier Type
type ExprL loc = Expression VarIdentifier (Typed loc)

type Lineage = [(GIdentifier,ModuleTyVarId)] -- trace of parent declarations

updCstrState :: (CstrState -> CstrState) -> TCstr -> TCstr
updCstrState f (DelayedK c arr) = DelayedK (updCstrState f c) arr
updCstrState f (TcK c st) = TcK c (f st)
updCstrState f (CheckK c st) = CheckK c (f st)
updCstrState f (HypK c st) = HypK c (f st)

newLineage :: Lineage -> TCstr -> TCstr
newLineage l = updCstrState (\(x1,x2,x3,x4,_) -> (x1,x2,x3,x4,l))

-- (is annotation,expression class,is leak,decKind,lineage)
type CstrState = (Bool,ExprC,Bool,DecKind,Lineage)

data TCstr
    = TcK
        TcCstr -- constraint
        CstrState
    | DelayedK
        TCstr -- a constraint
        (Int,SecrecErrArr) -- an error message with updated context
        --ModuleTcEnv -- optional recursive declarations only in scope for solving this constraint
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
    hashWithSalt i (DelayedK c _) = i `hashWithSalt` (1::Int) `hashWithSalt` c
    hashWithSalt i (CheckK c _) = i `hashWithSalt` (2::Int) `hashWithSalt` c
    hashWithSalt i (HypK c _) = i `hashWithSalt` (3::Int) `hashWithSalt` c
 
coreTCstr :: TCstr -> TCstr
coreTCstr (DelayedK c _) = coreTCstr c
coreTCstr c = c
 
instance Hashable EntryEnv
 
instance Eq TCstr where
    (DelayedK c1 _) == (DelayedK c2 _) = c1 == c2
    (TcK x b1) == (TcK y b4) = x == y && b1 == b4
    (HypK x b1) == (HypK y b4) = x == y && b1 == b4 
    (CheckK x b1) == (CheckK y b4) = x == y && b1 == b4 
    x == y = False
    
instance Ord TCstr where
    compare (DelayedK c1 _) (DelayedK c2 _) = c1 `compare` c2
    compare (TcK x b1) (TcK y b4) = mconcat [compare x y,compare b1 b4]
    compare (HypK x b1) (HypK y b4) = mconcat [compare x y,compare b1 b4]
    compare (CheckK x b1) (CheckK y b4) = mconcat [compare x y,compare b1 b4]
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)

priorityTCstr :: VarsIdTcM m => TCstr -> TCstr -> TcM m Ordering
priorityTCstr (DelayedK c1 _) (DelayedK c2 _) = priorityTCstr c1 c2
priorityTCstr (TcK c1 _) (TcK c2 _) = priorityTcCstr c1 c2
priorityTCstr (HypK x _) (HypK y _) = return $ compare x y
priorityTCstr (CheckK x _) (CheckK y _) = return $ compare x y
priorityTCstr (TcK {}) y  = return LT
priorityTCstr x (TcK {})  = return GT
priorityTCstr (HypK {}) y = return LT
priorityTCstr x (HypK {}) = return GT

priorityTcCstr :: VarsIdTcM m => TcCstr -> TcCstr -> TcM m Ordering
priorityTcCstr k1 k2 = do
    mul1 <- isMultipleSubstsTcCstr k1
    mul2 <- isMultipleSubstsTcCstr k2
    case (mul1,mul2) of
        (True,False) -> return GT
        (False,True) -> return LT
        (True,True) -> priorityMultipleSubsts k1 k2
        (False,False) -> priorityTcCstr' k1 k2 
priorityTcCstr' (isGlobalTcCstr -> True) (isGlobalTcCstr -> False) = return GT
priorityTcCstr' (isGlobalTcCstr -> False) (isGlobalTcCstr -> True) = return LT
priorityTcCstr' (isValidTcCstr -> True) (isValidTcCstr -> False) = return GT
priorityTcCstr' (isValidTcCstr -> False) (isValidTcCstr -> True) = return LT
priorityTcCstr' c1 c2 = return $ compare c1 c2

priorityMultipleSubsts :: MonadIO m => TcCstr -> TcCstr -> TcM m Ordering
priorityMultipleSubsts c1@(MultipleSubstitutions vs1 _) c2@(MultipleSubstitutions vs2 _) = do
    x1::Set VarIdentifier <- fvsSet vs1
    x2::Set VarIdentifier <- fvsSet vs2
    case compare (Set.size x1) (Set.size x2) of
        LT -> return LT
        GT -> return GT
        EQ -> return $ compare c1 c2

isValidTcCstr (IsValid {}) = True
isValidTcCstr (NotEqual {}) = True
isValidTcCstr _ = False

ppExprTy e = do
    ppe <- pp e
    ppl <- pp (loc e)
    return $ ppe <+> text "::" <+> ppl
ppVarTy v = ppExprTy (varExpr v)

instance PP m VarIdentifier => PP m TcCstr where
    pp (TDec isTplt n ts x) = do
        ppn <- pp n
        ppts <- (mapM pp ts) 
        ppx <- pp x
        return $ text "tdec" <+> ppn <+> sepBy space ppts <+> char '=' <+> ppx
    pp (PDec n specs ts r x doCoerce xs) = do
        ppr <- pp r
        ppn <- pp n
        ppspecs <- mapM pp $ maybe [] id specs
        ppts <- mapM (ppVariadicArg ppExprTy) ts
        ppx <- pp x
        let ppCoerce = if doCoerce then text "~~>" else text "-->"
        ppxs <- mapM ppExprTy xs
        return $ ppr <+> ppn <+> abrackets (sepBy comma ppspecs) <+> parens (sepBy comma ppts) <+> char '=' <+> ppx <+> ppCoerce <+> parens (sepBy comma ppxs)
    pp (Equals t1 t2) = do
        pp1 <- pp t1
        pp2 <- pp t2
        return $ text "equals" <+> pp1 <+> pp2
    pp (Coerces e1 v2) = do
        pp1 <- ppExprTy e1
        pp2 <- ppVarTy v2
        return $ text "coerces" <+> pp1 <+> pp2
    pp (CoercesSecDimSizes e1 v2) = do
        pp1 <- ppExprTy e1
        pp2 <- ppVarTy v2
        return $ text "coercessecdimsizes" <+> pp1 <+> pp2
    pp (CoercesNSecDimSizes exs) = do
        pp1 <- (mapM (ppExprTy . fst) exs)
        pp2 <- (mapM (ppVarTy . snd) exs)
        return $ text "coerces2secdimsizes" <+> sepBy comma pp1 <+> char '=' <+> sepBy comma pp2
    pp (CoercesLit e) = do
        ppe <- ppExprTy e
        return $ text "coerceslit" <+> ppe
    pp (CoercesN exs) = do
        pp1 <- (mapM (ppExprTy . fst) exs)
        pp2 <- (mapM (ppVarTy . snd) exs)
        return $ text "coercesn" <+> sepBy comma pp1 <+> char '=' <+> sepBy comma pp2
    pp (Unifies t1 t2) = do
        pp1 <- pp t1
        pp2 <- pp t2
        return $ text "unifies" <+> pp1 <+> pp2
    pp (Assigns t1 t2) = do
        pp1 <- pp t1
        pp2 <- pp t2
        return $ text "assigns" <+> pp1 <+> pp2
    pp (SupportedPrint ts xs) = do
        ppts <- mapM pp ts
        ppxs <- mapM pp xs
        return $ text "print" <+> sepBy space ppts <+> sepBy space ppxs
    pp (ProjectStruct t a x) = do
        ppt <- pp t
        ppa <- pp a
        ppx <- pp x
        return $ ppt <> char '.' <> ppa <+> char '=' <+> ppx
    pp (ProjectMatrix t as x) = do
        pp1 <- pp t
        pp2 <- mapM pp as
        pp3 <- pp x
        return $ pp1 <> brackets (sepBy comma pp2) <+> char '=' <+> pp3
    pp (MultipleSubstitutions v s) = do
        pp1 <- pp v
        let f2 (x,y,z) = do
            ppx <- pp x
            ppy <- pp y
            ppz <- pp z
            return $ ppx $+$ nest 4 (text "=>" $+$ ppy <+> text ":" <+> ppz)
        pp2 <- (mapM f2 s)
        return $ text "multiplesubstitutions" <+> pp1 <+> vcat pp2
    pp (MatchTypeDimension d sz) = do
        pp1 <- pp d
        pp2 <- pp sz
        return $ text "matchtypedimension" <+> pp1 <+> pp2
    pp (IsValid c) = liftM (text "isvalid" <+>) (pp c)
    pp (NotEqual e1 e2) = do
        pp1 <- pp e1
        pp2 <- pp e2
        return $ text "not equal" <+> pp1 <+> pp2
    pp (TypeBase t b) = do
        ppt <- pp t
        ppb <- pp b
        return $ text "typebase" <+> ppt <+> ppb
    pp (IsPublic b e) = do
        ppb <- pp b
        ppe <- pp e
        return $ text "ispublic" <+> ppb <+> ppe
    pp (IsPrivate b e) = do
        ppb <- pp b
        ppe <- pp e
        return $ text "isprivate" <+> ppb <+> ppe
    pp (Resolve e) = liftM (text "resolve" <+>) (pp e)
    pp (Default szs e) = do
        pp1 <- pp szs
        pp2 <- ppExprTy e
        return $ text "default" <+> pp1 <+> pp2
    pp (ToMultiset t r) = do
        ppt <- pp t
        ppr <- pp r
        return $ text "tomultiset" <+> ppt <+> ppr

instance PP m VarIdentifier => PP m CheckCstr where
    pp (CheckAssertion c) = liftM (text "checkAssertion" <+>) (pp c)

instance PP m VarIdentifier => PP m HypCstr where
    pp (HypCondition c) = do
        pp1 <- pp c
        return $ text "hypothesis" <+> pp1
    pp (HypNotCondition c) = do
        pp1 <- pp c
        return $ text "hypothesis" <+> char '!' <> pp1
    pp (HypEqual e1 e2) = do
        pp1 <- pp e1
        pp2 <- pp e2
        return $ text "hypothesis" <+> pp1 <+> text "==" <+> pp2

instance PP m VarIdentifier => PP m TCstr where
    pp (DelayedK c f) = do
        pp1 <- pp c
        return $ text "delayed" <+> pp1
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
    
instance PP m VarIdentifier => PP m ArrayProj where
    pp (ArraySlice i1 i2) = do
        pp1 <- pp i1
        pp2 <- pp i2
        return $ pp1 <> char ':' <> pp2
    pp (ArrayIdx w) = pp w
    
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m ArrayProj where
    traverseVars f (ArraySlice i1 i2) = do
        i1' <- f i1
        i2' <- f i2
        return $ ArraySlice i1' i2'
    traverseVars f (ArrayIdx w) = do
        w' <- f w
        return $ ArrayIdx w'
    
instance PP m VarIdentifier => PP m [Type] where
    pp xs = do
        pxs <- mapM pp xs
        return $ brackets $ sepBy comma pxs
    
instance PP m VarIdentifier => PP m [(Type,IsVariadic)] where
    pp xs = do
        pp1 <- mapM (ppVariadicArg pp) xs
        return $ parens $ sepBy comma pp1
instance PP m VarIdentifier => PP m [(Constrained Var,IsVariadic)] where
    pp xs = do
        pp1 <- mapM (ppVariadicArg pp) xs
        return $ parens $ sepBy comma pp1
    
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m [Type] where
    traverseVars f xs = mapM f xs
    
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m [(Type, IsVariadic)] where
    traverseVars f xs = mapM f xs
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m [(Constrained Var, IsVariadic)] where
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
  
instance PP m VarIdentifier => PP m ArrayIndex where
    pp NoArrayIndex = return PP.empty
    pp (DynArrayIndex e) = pp e
    
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m ArrayIndex where
    traverseVars f NoArrayIndex = return NoArrayIndex
    traverseVars f (DynArrayIndex e) = do
        e' <- f e
        return $ DynArrayIndex e'

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
    
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m TcCstr where
    traverseVars f (TDec isTplt n args x) = do
        n' <- f n
        args' <- mapM f args
        x' <- f x
        return $ TDec isTplt n' args' x'
    traverseVars f (PDec n ts args ret x doCoerce xs) = do
        n' <- f n
        x' <- f x
        ts' <- mapM (mapM (mapFstM f)) ts
        args' <- mapM (mapFstM f) args
        ret' <- f ret
        xs' <- mapM f xs
        return $ PDec n' ts' args' ret' x' doCoerce xs'
    traverseVars f (Equals t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Equals t1' t2'
    traverseVars f (Coerces e1 v2) = do
        e1' <- f e1
        v2' <- f v2
        return $ Coerces e1' v2'
    traverseVars f (CoercesSecDimSizes e1 e2) = do
        e1' <- f e1
        e2' <- f e2
        return $ CoercesSecDimSizes e1' e2'
    traverseVars f (CoercesN exs) = do
        exs' <- mapM f exs
        return $ CoercesN exs'
    traverseVars f (CoercesNSecDimSizes exs) = do
        exs' <- mapM f exs
        return $ CoercesNSecDimSizes exs'
    traverseVars f (CoercesLit e) = do
        e' <- f e
        return $ CoercesLit e'
    traverseVars f (Unifies t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Unifies t1' t2'
    traverseVars f (Assigns t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Assigns t1' t2'
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
    traverseVars f (MultipleSubstitutions v ss) = do
        v' <- f v
        ss' <- mapM f ss
        return $ MultipleSubstitutions v' ss'
    traverseVars f (MatchTypeDimension t d) = do
        t' <- f t
        d' <- f d
        return $ MatchTypeDimension t' d'
    traverseVars f (IsValid c) = do
        c' <- f c
        return $ IsValid c'
    traverseVars f (NotEqual e1 e2) = do
        e1' <- f e1
        e2' <- f e2
        return $ NotEqual e1' e2'
    traverseVars f (IsPublic b c) = do
        b' <- f b
        c' <- f c
        return $ IsPublic b' c'
    traverseVars f (IsPrivate b c) = do
        b' <- f b
        c' <- f c
        return $ IsPrivate b' c'
    traverseVars f (Resolve t) = do
        t' <- f t
        return $ Resolve t'
    traverseVars f (Default szs t) = do
        szs' <- mapM f szs
        t' <- f t
        return $ Default szs' t'
    traverseVars f (ToMultiset t r) = do
        t' <- f t
        r' <- f r
        return $ ToMultiset t' r'
    traverseVars f (TypeBase t b) = do
        t' <- f t
        b' <- f b
        return $ TypeBase t' b'

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m CheckCstr where
    traverseVars f (CheckAssertion c) = do
        c' <- f c
        return $ CheckAssertion c'

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m HypCstr where
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

instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m TCstr where
    traverseVars f (DelayedK c err) = do
        c' <- f c
        return $ DelayedK c' err
    traverseVars f (TcK k st) = do
        k' <- f k
        return $ TcK k' st
    traverseVars f (CheckK k st) = do
        k' <- f k
        return $ CheckK k' st
    traverseVars f (HypK k st) = do
        k' <- f k
        return $ HypK k' st

type IOCstrGraph = Gr LocIOCstr ()
type LocIOCstr = Loc Position IOCstr

type TCstrGraph = Gr LocTCstr ()
type LocTCstr = Loc Position TCstr

-- | Template constraint dictionary
-- a dictionary with a set of inferred constraints and resolved constraints
data TDict = TDict
    { tCstrs :: IOCstrGraph -- a list of constraints
    , tChoices :: Set Int -- set of choice constraints that have already been branched
    , tSubsts :: TSubsts -- variable substitions
    , tRec :: ModuleTcEnv -- recursive environment
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

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m TCstrGraph where
    traverseVars f g = nmapM f g

instance (PP m VarIdentifier, GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m PureTDict where
    traverseVars f (PureTDict ks ss rec) = do
        ks' <- f ks
        ss' <- f ss
        rec' <- f rec
        return $ PureTDict ks' ss' rec'

fromPureTDict :: MonadIO m => PureTDict -> TcM m TDict
fromPureTDict (PureTDict g ss rec) = do
    g' <- fromPureCstrs g
    return $ TDict g' Set.empty ss rec

fromPureCstrs :: MonadIO m => TCstrGraph -> TcM m IOCstrGraph
fromPureCstrs g = do
    (g',is) <- runStateT (mapGrM newIOCstr g) Map.empty
    let g'' = gmap (\(ins,j,x,outs) -> (fmapSnd (is!) ins,j,x,fmapSnd (is!) outs)) g'
    return g''
  where
    newIOCstr (ins,i,Loc l k,outs) = do
        mn <- lift $ newModuleTyVarId
        st <- lift $ liftIO $ newIdRef mn Unevaluated
        let j = hashModuleTyVarId $ uniqId st
        State.modify $ \is -> Map.insert i j is
        return (ins,j,Loc l $ IOCstr k st,outs)

toPureCstrs :: IOCstrGraph -> TCstrGraph
toPureCstrs = nmap (fmap kCstr)

toPureTDict :: TDict -> PureTDict
toPureTDict (TDict ks _ ss rec) = PureTDict (toPureCstrs ks) ss rec

flattenIOCstrGraph :: IOCstrGraph -> [LocIOCstr]
flattenIOCstrGraph = map snd . labNodes

flattenIOCstrGraphSet :: IOCstrGraph -> Set LocIOCstr
flattenIOCstrGraphSet = Set.fromList . flattenIOCstrGraph

-- | mappings from variables to current substitution
newtype TSubsts = TSubsts { unTSubsts :: Map VarIdentifier Type } deriving (Eq,Show,Ord,Typeable,Data,Generic)
instance Binary TSubsts
instance Hashable TSubsts

--instance Monoid TSubsts where
--    mempty = TSubsts Map.empty
--    mappend (TSubsts x) (TSubsts y) = TSubsts (x `Map.union` y)

instance PP m VarIdentifier => PP m TSubsts where
    pp = ppTSubsts

instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m TSubsts where
    traverseVars f (TSubsts xs) = varsBlock $ liftM (TSubsts . Map.fromList) $ aux $ Map.toList xs
        where
        aux [] = return []
        aux ((k,v):xs) = do
            k' <- inLHS $ f k
            v' <- f v
            xs' <- aux xs
            return ((k',v'):xs')

emptyTDict :: TDict
emptyTDict = TDict Graph.empty Set.empty emptyTSubsts mempty

emptyPureTDict :: PureTDict
emptyPureTDict = PureTDict Graph.empty emptyTSubsts mempty

emptyTSubsts :: TSubsts
emptyTSubsts = TSubsts Map.empty

ioCstrId :: IOCstr -> Int
ioCstrId = hashModuleTyVarId . uniqId . kStatus

ioCstrUnique :: IOCstr -> ModuleTyVarId
ioCstrUnique = uniqId . kStatus

instance (Vars VarIdentifier m loc,Vars VarIdentifier m a) => Vars VarIdentifier m (Loc loc a) where
    traverseVars f (Loc l a) = do
        l' <- f l
        a' <- f a
        return $ Loc l' a'

newModuleTyVarId :: MonadIO m => TcM m ModuleTyVarId
newModuleTyVarId = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    return $ ModuleTyVarId mn i

freshVarId :: MonadIO m => Identifier -> Maybe Doc -> TcM m VarIdentifier
freshVarId n doc = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v' = VarIdentifier n (Just mn) (Just i) False doc
    return v'

freeVarId :: MonadIO m => Identifier -> Bool -> Maybe Doc -> TcM m VarIdentifier
freeVarId n isVariadic doc = do
    v <- freshVarId n doc
    addFree v isVariadic
    return v

type Frees = Map VarIdentifier IsVariadic

addFree :: MonadIO m => VarIdentifier -> Bool -> TcM m ()
addFree n isVariadic = do
    debugTc $ do
        ppn <- ppr n
        liftIO $ putStrLn $ "addFree " ++ ppn ++ " " ++ pprid isVariadic
    State.modify $ \env -> env { localFrees = Map.insert n isVariadic (localFrees env) }

removeFree :: MonadIO m => VarIdentifier -> TcM m ()
removeFree n = do
    debugTc $ do
        ppn <- ppr n
        liftIO $ putStrLn $ "removeFree " ++ ppn
    State.modify $ \env -> env { localFrees = Map.delete n (localFrees env) }

instance PP m VarIdentifier => PP m TDict where
    pp dict = do
        pp1 <- ppGrM pp (const $ return PP.empty) $ tCstrs dict
        pp2 <- ppTSubsts (tSubsts dict)
        return $ text "Constraints:" $+$ nest 4 pp1
              $+$ text "Substitutions:" $+$ nest 4 pp2

instance PP m VarIdentifier => PP m PureTDict where
    pp dict = do
        pp1 <- ppGrM pp (const $ return PP.empty) $ pureCstrs dict
        pp2 <- ppTSubsts (pureSubsts dict)
        return $ text "Constraints:" $+$ nest 4 pp1
              $+$ text "Substitutions:" $+$ nest 4 pp2

ppConstraints :: MonadIO m => IOCstrGraph -> TcM m Doc
ppConstraints d = do
    let ppK (Loc l c) = do
        s <- liftIO $ readIdRef $ kStatus c
        pre <- pp c
        case s of
            Evaluated rest t -> return $ pre <+> char '=' <+> text (show t)
            Unevaluated -> return $ pre
            Erroneous err -> return $ pre <+> char '=' <+> if isHaltError err then text "HALT" else text "ERROR"
    ss <- ppGrM ppK (const $ return PP.empty) d
    return ss

data VarIdentifier = VarIdentifier
        { varIdBase :: Identifier
        , varIdModule :: Maybe (Identifier,TyVarId)
        , varIdUniq :: Maybe TyVarId
        , varIdTok :: Bool -- if the variable is a token (not to be resolved) (only used for comparisons)
        , varIdPretty :: Maybe Doc -- for free variables introduced by typechecking
        }
    deriving (Typeable,Data,Show,Generic)

instance Binary VarIdentifier

instance Eq VarIdentifier where
    v1 == v2 = varIdUniq v1 == varIdUniq v2 && varIdBase v1 == varIdBase v2 && varIdModule v1 == varIdModule v2
instance Ord VarIdentifier where
    compare v1 v2 = mconcat [varIdBase v1 `compare` varIdBase v2,varIdUniq v1 `compare` varIdUniq v2,varIdModule v1 `compare` varIdModule v2]

varTok :: VarName VarIdentifier loc -> Bool
varTok (VarName _ n) = varIdTok n

mkVarId :: Identifier -> VarIdentifier
mkVarId s = VarIdentifier s Nothing Nothing False Nothing

instance Monad m => PP (TcM m) VarIdentifier where
    pp v = askOpts >>= flip ppVarId v

instance Monad m => PP (SecrecM m) VarIdentifier where
    pp v = ask >>= flip ppVarId v

instance PP Identity VarIdentifier where
    pp v = ppVarId defaultOptions v

ppVarId :: Monad m => Options -> VarIdentifier -> m Doc
ppVarId opts v = case varIdPretty v of
    Just s -> if debug opts
        then do
            pv <- ppVarId' v
            return $ pv <> char '#' <> s
        else return s
    Nothing -> ppVarId' v
  where
    f (x,blk) = do
        pp1 <- pp blk
        return $ text x <> char '.' <> pp1 <> char '.'
    ppVarId' (VarIdentifier n m Nothing _ _) = do
        ppo <- ppOpt m f
        return $ ppo <> text n
    ppVarId' (VarIdentifier n m (Just i) _ _) = do
        ppo <- ppOpt m f
        ppi <- pp i
        return $ ppo <> text n <> char '_' <> ppi

newtype TyVarId = TyVarId Integer deriving (Eq,Ord,Data,Generic)
instance Show TyVarId where
    show (TyVarId i) = show i
instance Monad m => PP m TyVarId where
    pp (TyVarId i) = pp i
instance Binary TyVarId
instance Hashable TyVarId where
    hashWithSalt i (TyVarId x) = hashWithSalt i x

instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m TyVarId where
    traverseVars f x = return x

uniqTyVarId :: IORef Integer
uniqTyVarId = unsafePerformIO (newIORef 0)
{-# NOINLINE uniqTyVarId #-}

resetTyVarId :: IO ()
resetTyVarId = do
    atomicModifyIORef' uniqTyVarId $ \x -> (0,0)
    return ()

newTyVarId :: IO TyVarId
newTyVarId = do
  r <- atomicModifyIORef' uniqTyVarId $ \x -> let z = x+1 in (z,z)
  return (TyVarId r)

hashTyVarId :: TyVarId -> Int
hashTyVarId (TyVarId i) = I# (hashInteger i)

secTypeKind :: SecType -> KindType
secTypeKind Public = PublicK
secTypeKind (Private _ k) = PrivateK k
secTypeKind (SVar _ k) = k

data SecType
    = Public -- ^ public domain
    | Private -- ^ private domain
        (DomainName VarIdentifier ()) -- ^ domain
        (KindName VarIdentifier ()) -- ^ kind
    | SVar VarIdentifier KindType
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary SecType
instance Hashable SecType

data KindType
    = PublicK
    | PrivateK (KindName VarIdentifier ()) -- a known kind
    | KVar VarIdentifier Bool -- a kind variable (bool = is only private)
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary KindType
instance Hashable KindType

isPrivateKind :: KindType -> Bool
isPrivateKind PublicK = False
isPrivateKind (PrivateK _) = True
isPrivateKind (KVar _ True) = True
isPrivateKind (KVar _ False) = False

tyDecClass :: Type -> DecClass
tyDecClass (DecT (DecType _ _ _ _ _ _ _ _ (ProcType _ _ _ _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ _ _ (FunType _ _ _ _ _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ _ _ (StructType _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ _ _ (AxiomType _ _ _ _ cl))) = cl
tyDecClass (DecT (DecType _ _ _ _ _ _ _ _ (LemmaType _ _ _ _ _ _ cl))) = cl
tyDecClass t = error $ "tyDecClass: " ++ show t

tyIsAnn t = let (DecClass b _ _ _) = tyDecClass t in b
tyIsInline t = let (DecClass _ b _ _) = tyDecClass t in b

decTypeFrees :: DecType -> Frees
decTypeFrees (DecType _ _ _ hvs hfs _ bfs _ _) = Map.unionWith (||) hfs bfs

decTypeId :: DecType -> Maybe (GIdentifier,ModuleTyVarId)
decTypeId d = case (decTypeDecId d,decTypeTyVarId d) of
    (Just x,Just y) -> Just (x,y)
    otherwise -> Nothing
    
decTypeDecId :: DecType -> Maybe GIdentifier
decTypeDecId (DecType _ _ _ _ _ _ _ _ d) = decTypeDecId' d
    where
    decTypeDecId' (ProcType _ (Left p) _ _ _ _ _) = Just $ PIden p
    decTypeDecId' (ProcType _ (Right o) _ _ _ _ _) = Just $ OIden $ funit o
    decTypeDecId' (LemmaType _ _ p _ _ _ _) = Just $ PIden p
    decTypeDecId' (FunType _ _ (Left p) _ _ _ _ _) = Just $ PIden p
    decTypeDecId' (FunType _ _ (Right o) _ _ _ _ _) = Just $ OIden $ funit o
    decTypeDecId' (StructType _ (TypeName _ s) _ _) = Just $ TIden s
    decTypeDecId' (AxiomType _ _ _ _ _) = Nothing
decTypeDecId d = Nothing

isLeakType :: Type -> Bool
isLeakType (DecT d) = isLeakDec d

isLeakDec :: DecType -> Bool
isLeakDec (DecType _ _ _ _ _ _ _ _ i) = isLeakInnerDec i

isLeakInnerDec :: InnerDecType -> Bool
isLeakInnerDec (ProcType {}) = False
isLeakInnerDec (FunType isLeak _ _ _ _ _ _ _) = isLeak
isLeakInnerDec (StructType {}) = False
isLeakInnerDec (AxiomType isLeak _ _ _ _) = isLeak
isLeakInnerDec (LemmaType isLeak _ _ _ _ _ _) = isLeak

decTyKind :: DecType -> DecKind
decTyKind (DecType _ _ _ _ _ _ _ _ i) = iDecTyKind i

iDecTyKind :: InnerDecType -> DecKind
iDecTyKind (ProcType {}) = PKind
iDecTyKind (FunType {}) = FKind
iDecTyKind (AxiomType {}) = AKind
iDecTyKind (StructType {}) = TKind
iDecTyKind (LemmaType {}) = LKind

data DecType
    = DecType -- ^ top-level declaration (used for template declaration and also for non-templates to store substitutions)
        ModuleTyVarId -- ^ unique template declaration id
        (Maybe (ModuleTyVarId,[Type])) -- is a recursive invocation = Just (original,expanded template type arguments)
        [(Constrained Var,IsVariadic)] -- ^ template variables
        PureTDict -- ^ constraints for the header
        Frees -- set of free internal constant variables generated when typechecking the header
        PureTDict -- ^ constraints for the template
        Frees -- set of free internal constant variables generated when typechecking the template
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
        Type -- return type
        [ProcedureAnnotation VarIdentifier (Typed Position)] -- ^ the procedure's annotations
        (Maybe [Statement VarIdentifier (Typed Position)]) -- ^ the procedure's body
        DecClass -- the type of procedure
    | FunType -- ^ procedure type
        Bool -- is leakage function
        Position
        PIdentifier
        [(Bool,Var,IsVariadic)] -- typed function arguments
        Type -- return type
        [ProcedureAnnotation VarIdentifier (Typed Position)] -- ^ the function's annotations
        (Maybe (Expression VarIdentifier (Typed Position))) -- ^ the function's body
        DecClass -- the type of function
    | StructType -- ^ Struct type
        Position -- ^ location of the procedure declaration
        SIdentifier
        (Maybe [Attribute VarIdentifier Type]) -- ^ typed arguments
        DecClass -- the type of struct
    | AxiomType
        Bool -- is leakage axiom
        Position
        [(Bool,Var,IsVariadic)] -- typed function arguments
        [ProcedureAnnotation VarIdentifier (Typed Position)] -- ^ the procedure's annotations
        DecClass
    | LemmaType -- ^ lemma type
        Bool -- is leakage
        Position
        VarIdentifier -- lemma's name
        [(Bool,Var,IsVariadic)] -- typed lemma arguments
        [ProcedureAnnotation VarIdentifier (Typed Position)] -- ^ the lemma's annotations
        (Maybe [Statement VarIdentifier (Typed Position)]) -- ^ the lemma's body
        DecClass -- the type of lemma
        
  deriving (Typeable,Show,Data,Generic,Eq,Ord)

isTemplateDecType :: DecType -> Bool
isTemplateDecType (DecType _ _ ts _ _ _ _ specs _) = not (null ts && null specs)
isTemplateDecType _ = False

isFunType :: Type -> Bool
isFunType (DecT d) = isFunDecType d
isFunType _ = False 

isFunDecType :: DecType -> Bool
isFunDecType (DecType _ _ _ _ _ _ _ specs (FunType {})) = True
isFunDecType _ = False

isFunInnerDecType :: InnerDecType -> Bool
isFunInnerDecType (FunType {}) = True
isFunInnerDecType _ = False

isNonRecursiveDecType :: DecType -> Bool
isNonRecursiveDecType (DecType i _ _ _ _ _ _ _ d) = not $ everything (||) (mkQ False aux) d
    where
    aux :: DecType -> Bool
    aux (DecType _ (Just (j,_)) _ _ _ _ _ _ _) = i == j
    aux d = False
isNonRecursiveDecType d = False

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

instance (PP m a,PP m VarIdentifier) => PP m (Constrained a) where
    pp = ppConstrained pp

ppConstrained :: PP m VarIdentifier => (a -> m Doc) -> Constrained a -> m Doc
ppConstrained f (Constrained t Nothing) = f t
ppConstrained f (Constrained t (Just c)) = do
    ft <- f t
    ppc <- pp c
    return $ ft <+> braces ppc

instance (MonadIO m,Vars VarIdentifier m a) => Vars VarIdentifier m (Constrained a) where
    traverseVars f (Constrained t e) = do
        t' <- f t
        e' <- inRHS $ f e
        return $ Constrained t' e'

data BaseType
    = TyPrim Prim
    | TApp SIdentifier [(Type,IsVariadic)] DecType -- template type application
    | MSet BaseType -- multiset type
    | BVar VarIdentifier
  deriving (Typeable,Show,Data,Eq,Ord,Generic)

instance Binary BaseType
instance Hashable BaseType

type CondExpression iden loc = (Expression iden loc)
type Cond = CondExpression VarIdentifier Type

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
    | BType -- ^ Type of base types
    | KType Bool -- ^ Type of kinds (isPrivateKind)
    | VAType Type Expr -- ^ Type of array types
    | StmtType (Set StmtClass) -- ^ Type of a @Statement@
    | ComplexT ComplexType
    | BaseT BaseType
    | SecT SecType
    | KindT KindType
    | DecT DecType
    | IDecT InnerDecType -- internal only
    | SysT SysType
    | VArrayT VArrayType -- for variadic array types
    | IdxT Expr -- for index expressions
    | CondType Type Cond -- a type with an invariant
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

tyOf :: Type -> Type
tyOf (IdxT e) = loc e
tyOf (SecT s) = KindT (secTypeKind s)
tyOf (KindT k) = KType (isPrivateKind k)
tyOf (ComplexT t) = TType (isNotVoid t)
tyOf (BaseT _) = BType
tyOf (DecT _) = DType
tyOf (VArrayT (VAVal ts b)) = VAType b (indexExpr $ toEnum $ length ts)
tyOf (VArrayT (VAVar v b sz)) = VAType b sz
tyOf (CondType t _) = tyOf t
tyOf t = error $ "unknown type for " ++ show t

constrainedType :: Type -> Maybe Cond -> Type
constrainedType t Nothing = t
constrainedType t (Just c) = CondType t c

ppOf a b = a <+> text "::" <+> b
ppTyped (a,b) = do
    ppa <- pp a
    ppb <- pp b
    return $ ppa `ppOf` ppb
ppFrees xs = do
    ppxs <- mapM pp $ Set.toList xs
    return $ text "Free variables:" <+> sepBy comma ppxs

instance PP m VarIdentifier => PP m VArrayType where
    pp (VAVal ts b) = do
        ppts <- mapM pp ts
        ppb <- pp b
        return $ brackets $ sepBy comma ppts <+> text "::" <+> ppb <> text "[[1]]"
    pp (VAVar v b sz) = do
        ppv <- pp v
        ppb <- pp b
        ppsz <- pp sz
        return $ parens (ppv <+> text "::" <+> ppb <> text "[[1]]" <> parens ppsz)

instance PP m VarIdentifier => PP m SecType where
    pp Public = return $ text "public"
    pp (Private d k) = pp d
    pp (SVar v k) = do
        ppv <- pp v
        ppk <- pp k
        return $ parens (ppv <+> text "::" <+> ppk)
        
ppAtt (Attribute t _ n szs) = do
    ppt <- pp t
    ppn <- pp n
    ppz <- pp szs
    return $ ppt <+> ppn <> ppz        

instance PP m VarIdentifier => PP m DecType where
    pp (DecType did isrec vars hdict hfrees dict frees specs body@(StructType _ n atts cl)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp21 <- pp hfrees
        pp3 <- pp hdict
        pp31 <- pp frees
        pp4 <- pp dict
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp n
        pp7 <- mapM pp specs
        pp8 <- ppOpt atts (liftM (braces . vcat) . mapM ppAtt)
        return $ pp1 <+> pp2
            $+$ text "Frees:" <+> pp21
            $+$ pp3
            $+$ text "Frees:" <+> pp31
            $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ text "struct" <+> pp6 <> abrackets (sepBy comma pp7) <+> pp8
    pp (DecType did isrec vars hdict hfrees dict frees [] body@(ProcType _ (Left n) args ret ann stmts _)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp21 <- pp hfrees
        pp3 <- pp hdict
        pp31 <- pp frees
        pp4 <- pp dict
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp ret
        pp7 <- pp n
        pp8 <- mapM ppConstArg args
        pp9 <- pp ann
        pp10 <- ppOpt stmts (liftM braces . pp)
        return $ pp1 <+> pp2
            $+$ text "Frees:" <+> pp21
            $+$ pp3
            $+$ text "Frees:" <+> pp31
            $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ pp6 <+> pp7 <> parens (sepBy comma pp8)
            $+$ pp9
            $+$ pp10
    pp (DecType did isrec vars hdict hfrees dict frees [] body@(ProcType _ (Right n) args ret ann stmts _)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp21 <- pp hfrees
        pp3 <- pp hdict
        pp31 <- pp frees
        pp4 <- pp dict
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp ret
        pp7 <- pp n
        pp8 <- mapM ppConstArg args
        pp9 <- pp ann
        pp10 <- ppOpt stmts (liftM braces . pp)
        return $ pp1 <+> pp2
            $+$ text "Frees:" <+> pp21
            $+$ pp3
            $+$ text "Frees:" <+> pp31
            $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ pp6 <+> text "operator" <+> pp7 <> parens (sepBy comma pp8)
            $+$ pp9
            $+$ pp10
    pp (DecType did isrec vars hdict hfrees dict frees [] body@(FunType isLeak _ (Left n) args ret ann stmts _)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp21 <- pp hfrees
        pp3 <- pp hdict
        pp31 <- pp frees
        pp4 <- pp dict
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp ret
        pp7 <- pp n
        pp8 <- mapM ppConstArg args
        pp9 <- pp ann
        pp10 <- ppOpt stmts (liftM braces . pp)
        return $ ppLeak isLeak (pp1 <+> pp2
            $+$ text "Frees:" <+> pp21
            $+$ pp3
            $+$ text "Frees:" <+> pp31
            $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ pp6 <+> pp7 <> parens (sepBy comma pp8)
            $+$ pp9
            $+$ pp10)
    pp (DecType did isrec vars hdict hfrees dict frees [] body@(FunType isLeak _ (Right n) args ret ann stmts _)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp21 <- pp hfrees
        pp3 <- pp hdict
        pp31 <- pp frees
        pp4 <- pp dict
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- pp ret
        pp7 <- pp n
        pp8 <- mapM ppConstArg args
        pp9 <- pp ann
        pp10 <- ppOpt stmts (liftM braces . pp)
        return $ ppLeak isLeak (pp1 <+> pp2
            $+$ text "Frees:" <+> pp21
            $+$ pp3
            $+$ text "Frees:" <+> pp31
            $+$ pp4
            $+$ text "template" <> abrackets (sepBy comma pp5)
            $+$ pp6 <+> text "operator" <+> pp7 <> parens (sepBy comma pp8)
            $+$ pp9
            $+$ pp10)
    pp (DecType did isrec vars hdict hfrees dict frees [] body@(AxiomType isLeak _ args ann _)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp21 <- pp hfrees
        pp3 <- pp hdict
        pp31 <- pp frees
        pp4 <- pp dict
        pp5 <- mapM (ppVariadicArg ppTpltArg) vars
        pp6 <- mapM ppConstArg args
        pp7 <- pp ann
        return $ ppLeak isLeak (pp1 <+> pp2
            $+$ text "Frees:" <+> pp21
            $+$ pp3
            $+$ text "Frees:" <+> pp31
            $+$ pp4
            $+$ text "axiom" <> abrackets (sepBy comma pp5)
            <+> parens (sepBy comma $ pp6) $+$ pp7)
    pp (DecType did isrec vars hdict hfrees dict frees [] body@(LemmaType isLeak _ n args ann stmts _)) = do
        pp1 <- pp did
        pp2 <- pp isrec
        pp21 <- pp hfrees
        pp3 <- pp hdict
        pp31 <- pp frees
        pp4 <- pp dict
        pp5 <- pp n
        pp6 <- mapM (ppVariadicArg ppTpltArg) vars
        pp7 <- mapM ppConstArg args
        pp8 <- pp ann
        pp9 <- ppOpt stmts (liftM braces . pp)
        return $ ppLeak isLeak (pp1 <+> pp2
            $+$ text "Frees:" <+> pp21
            $+$ pp3
            $+$ text "Frees:" <+> pp31
            $+$ pp4
            $+$ text "lemma" <+> pp5 <+> abrackets (sepBy comma pp6)
            <+> parens (sepBy comma pp7)
            $+$ pp8
            $+$ pp9)
    pp (DVar v) = pp v
    pp d = error $ "pp: " ++ show d

ppConstArg (isConst,(VarName t n),isVariadic) = do
    ppt <- pp t
    ppn <- pp n
    return $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)

instance PP m VarIdentifier => PP m InnerDecType where
    pp (StructType _ n atts cl) = do
        ppn <- pp n
        ppo <- ppOpt atts (liftM (braces . vcat) . mapM ppAtt)
        return $ text "struct" <+> ppn <+> ppo
    pp (ProcType _ (Left n) args ret ann stmts _) = do
        ppret <- pp ret
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            return $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        return $ ppret <+> ppn <> parens (sepBy comma pp1) $+$ ppann $+$ ppo
    pp (ProcType _ (Right n) args ret ann stmts _) = do
        ppret <- pp ret
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            return $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        return $ ppret <+> text "operator" <+> ppn <> parens (sepBy comma pp1) $+$ ppann $+$ ppo
    pp (FunType isLeak _ (Left n) args ret ann stmts _) = do
        ppret <- pp ret
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            return $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        return $ ppLeak isLeak (ppret <+> ppn <> parens (sepBy comma pp1) $+$ ppann $+$ ppo)
    pp (FunType isLeak _ (Right n) args ret ann stmts _) = do
        ppret <- pp ret
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            return $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        return $ ppLeak isLeak (ppret <+> text "operator" <+> ppn <> parens (sepBy comma pp1) $+$ ppann $+$ ppo)
    pp (AxiomType isLeak _ args ann _) = do
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            return $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        return $ ppLeak isLeak (text "axiom" <+> parens (sepBy comma pp1) $+$ ppann)
    pp (LemmaType isLeak _ n args ann stmts _) = do
        ppn <- pp n
        let f1 (isConst,(VarName t n),isVariadic) = do
            ppt <- pp t
            ppn <- pp n
            return $ ppConst isConst (ppVariadic (ppt) isVariadic <+> ppn)
        pp1 <- mapM f1 args
        ppann <- pp ann
        ppo <- ppOpt stmts (liftM braces . pp)
        return $ ppLeak isLeak (text "lemma" <+> ppn <+> parens (sepBy comma pp1) $+$ ppann $+$ ppo)
        
instance PP m VarIdentifier => PP m BaseType where
    pp (TyPrim p) = pp p
    pp (TApp n ts d) = do
        ppn <- pp n
        ppts <- mapM (ppVariadicArg pp) ts
        ppd <- pp d
        return $ parens (ppn <> abrackets (sepBy comma $ ppts) <+> ppd)
    pp (MSet t) = do
        ppt <- pp t
        return $ text "multiset" <> braces ppt
    pp (BVar v) = pp v
instance PP m VarIdentifier => PP m ComplexType where
    pp Void = return $ text "void"
    pp (CType s t d) = do
        pps <- pp s
        ppt <- pp t
        ppd <- pp d
        return $ pps <+> ppt <> brackets (brackets ppd)
    pp (CVar v b) = pp v
instance PP m VarIdentifier => PP m SysType where
    pp t@(SysPush {}) = return $ text (show t)
    pp t@(SysRet {}) =  return $ text (show t)
    pp t@(SysRef {}) =  return $ text (show t)
    pp t@(SysCRef {}) = return $ text (show t)

instance PP m VarIdentifier => PP m Type where
    pp t@(NoType msg) = return $ text "no type" <+> text msg
    pp (VAType t sz) = do
        ppt <- pp t
        ppsz <- pp sz
        return $ parens $ ppt <> text "..." <> nonemptyParens ppsz
    pp t@(TType b) = return $ text "complex type" <+> ppid b
    pp t@BType = return $ text "base type"
    pp t@DType = return $ text "declaration type"
    pp t@(KindT k) = pp k
    pp t@(KType b) = return $ text "kind type" <+> ppid b
    pp t@(StmtType {}) = return $ text (show t)
    pp (BaseT b) = pp b
    pp (ComplexT c) = pp c
    pp (SecT s) = pp s
    pp (DecT d) = pp d
    pp (IDecT d) = pp d
    pp (SysT s) = pp s
    pp (IdxT e) = pp e
    pp (VArrayT a) = pp a
    pp (CondType t c) = ppConstrained pp (Constrained t $ Just c)

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

instance PP m VarIdentifier => PP m TypeClass where
    pp KindStarC = return $ text "kind star"
    pp (VArrayStarC t) = liftM (text "array star of" <+>) (pp t)
    pp KindC = return $ text "kind"
    pp DomainC = return $ text "domain"
    pp TypeStarC = return $ text "type star"
    pp (ExprC c) = liftM (text "index expression" <+>) (pp c)
    pp TypeC = return $ text "complex type"
    pp SysC = return $ text "system call parameter"
    pp DecC = return $ text "declaration"
    pp (VArrayC t) = liftM (text "array" <+>) (pp t)

typeClass :: String -> Type -> TypeClass
typeClass msg (CondType t _) = typeClass msg t
typeClass msg (TType b) = TypeStarC
typeClass msg (VAType b _) = VArrayStarC (typeClass msg b)
typeClass msg BType = TypeStarC
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
isStruct (DecType _ _ _ _ _ _ _ _ (StructType {})) = True
isStruct _ = False

isStructTemplate :: Type -> Bool
isStructTemplate (DecT (DecType _ _ _ _ _ _ _ _ (StructType {}))) = True
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

isBoolType :: Type -> Bool
isBoolType (BaseT b) = isBoolBaseType b
isBoolType _ = False

isBoolBaseType :: BaseType -> Bool
isBoolBaseType (TyPrim (DatatypeBool _)) = True
isBoolBaseType _ = False

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

instance PP m VarIdentifier => PP m StmtClass where
    pp = return . text . show

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m StmtClass where
    traverseVars f c = return c
  
instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m SecType where
    traverseVars f Public = return Public
    traverseVars f (Private d k) = return $ Private d k
    traverseVars f (SVar v k) = do
        v' <- f v
        k' <- f k
        return $ SVar v' k'
    substL (SVar v _) | not (varIdTok v) = return $ Just v
    substL e = return $ Nothing

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m [TCstr] where
    traverseVars f xs = mapM f xs
    
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m [TcCstr] where
    traverseVars f xs = mapM f xs

instance PP m VarIdentifier => PP m [TCstr] where
    pp xs = do
        pxs <- mapM pp xs
        return $ brackets (sepBy comma pxs)
    
instance PP m VarIdentifier => PP m [TcCstr] where
    pp xs = do
        pxs <- mapM pp xs
        return $ brackets (sepBy comma pxs)

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m DecClass where
    traverseVars f (DecClass x i y z) = do
        x' <- f x
        i' <- f i
        y' <- f y
        z' <- f z
        return (DecClass x' i' y' z')

instance PP m VarIdentifier => PP m DecClass where
    pp (DecClass False inline r w) = do
        ppr <- pp r
        ppw <- pp w
        return $ text "procedure" <+> ppInline inline <+> ppr <+> ppw
    pp (DecClass True inline r w) = do
        ppr <- pp r
        ppw <- pp w
        return $ text "annotation procedure" <+> ppInline inline <+> ppr <+> ppw

ppInline True = text "inline"
ppInline False = text "noinline"

instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m DecType where
    traverseVars f (DecType tid isRec vs hd hfrees d frees spes t) = do
        isRec' <- mapM f isRec
        varsBlock $ do
            vs' <- inLHS $ mapM f vs
            hfrees' <- liftM Map.fromList $ mapM f $ Map.toList hfrees
            frees' <- liftM Map.fromList $ mapM f $ Map.toList frees
            hd' <- f hd
            d' <- f d
            spes' <- mapM f spes
            t' <- f t
            return $ DecType tid isRec' vs' hd' hfrees' d' frees' spes' t'
    traverseVars f (DVar v) = do
        v' <- f v
        return $ DVar v'
    substL (DVar v) | not (varIdTok v) = return $ Just v
    substL _ = return Nothing

instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m InnerDecType where
    traverseVars f (ProcType p n vs t ann stmts c) = varsBlock $ do
        n' <- f n
        vs' <- inLHS $ mapM f vs
        t' <- f t
        ann' <- mapM f ann
        stmts' <- f stmts
        c' <- f c
        return $ ProcType p n' vs' t' ann' stmts' c'
    traverseVars f (LemmaType isLeak p n vs ann stmts c) = varsBlock $ do
        n' <- f n
        vs' <- inLHS $ mapM f vs
        ann' <- mapM f ann
        stmts' <- f stmts
        c' <- f c
        return $ LemmaType isLeak p n' vs' ann' stmts' c'
    traverseVars f (FunType isLeak p n vs t ann stmts c) = varsBlock $ do
        n' <- f n
        vs' <- inLHS $ mapM f vs
        t' <- f t
        ann' <- mapM f ann
        stmts' <- f stmts
        c' <- f c
        return $ FunType isLeak p n' vs' t' ann' stmts' c'
    traverseVars f (AxiomType isLeak p ps ann c) = varsBlock $ do
        ps' <- inLHS $ mapM f ps
        ann' <- mapM f ann
        c' <- f c
        return $ AxiomType isLeak p ps' ann' c'
    traverseVars f (StructType p n as cl) = varsBlock $ do
        n' <- f n
        as' <- inLHS $ mapM f as
        cl' <- f cl
        return $ StructType p n' as' cl'
    
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m BaseType where
    traverseVars f (TyPrim p) = do
        p' <- f p
        return $ TyPrim p'
    traverseVars f (MSet t) = do
        t' <- f t
        return $ MSet t'
    traverseVars f (TApp n ts d) = do
        n' <- f n
        ts' <- mapM f ts
        d' <- f d
        return $ TApp n' ts' d'
    traverseVars f (BVar v) = do
        v' <- f v
        return $ BVar v'
    substL (BVar v) | not (varIdTok v) = return $ Just v
    substL e = return Nothing
 
instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m VArrayType where
    traverseVars f (VAVal ts b) = do
        ts' <- f ts
        b' <- f b
        return $ VAVal ts' b'
    traverseVars f (VAVar v b sz) = do
        v' <- f v
        b' <- f b
        sz' <- f sz
        return $ VAVar v' b' sz'
    substL (VAVar v _ _) | not (varIdTok v) = return $ Just v
    substL e = return Nothing
 
instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m ComplexType where
    traverseVars f (CType s t d) = do
        s' <- f s
        t' <- f t
        d' <- f d
        return $ CType s' t' d' 
    traverseVars f (CVar v b) = do
        v' <- f v
        b' <- f b
        return $ CVar v' b'
    traverseVars f Void = return Void
    substL (CVar v b) | not (varIdTok v) = return $ Just v
    substL e = return Nothing

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m SysType where
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

instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m KindType where
    traverseVars f PublicK = return PublicK
    traverseVars f (PrivateK k) = return $ PrivateK k
    traverseVars f (KVar k b) = do
        k' <- f k
        return $ KVar k' b
    substL (KVar v _) | not (varIdTok v) = return $ Just v
    substL e = return Nothing

instance PP m VarIdentifier => PP m KindType where
    pp PublicK = return $ text "public"
    pp (PrivateK k) = pp k
    pp (KVar k True) = liftM (text "nonpublic" <+>) (pp k)
    pp (KVar k False) = pp k
    
instance (PP m VarIdentifier,GenVar VarIdentifier m,MonadIO m) => Vars VarIdentifier m Type where
    traverseVars f (NoType x) = return (NoType x)
    traverseVars f (TType b) = return (TType b)
    traverseVars f (VAType t sz) = do
        t' <- f t
        sz' <- f sz
        return $ VAType t' sz'
    traverseVars f DType = return DType
    traverseVars f BType = return BType
    traverseVars f (KType b) = return $ KType b
    traverseVars f (KindT s) = do
        s' <- f s
        return $ KindT s'
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
    --substL (BaseT (BVar v)) = return $ Just v
    --substL (SecT (SVar v _)) = return $ Just v
    --substL (ComplexT (CVar v)) = return $ Just v
    --substL (DecT (DVar v)) = return $ Just v
    --substL (IdxT (RVariablePExpr _ v)) = return $ Just $ varNameId v
    --substL (VArrayT (VAVar v _ _)) = return $ Just v
    substL e = return Nothing

data DecClass
    -- A procedure
    = DecClass
        Bool -- is an annotation
        Bool -- perform inlining
        (Map VarIdentifier Type) -- read global variables
        (Map VarIdentifier Type) -- written global variables
  deriving (Show,Data,Typeable,Eq,Ord,Generic)
instance Binary DecClass
instance Hashable DecClass

instance Monoid DecClass where
    mempty = DecClass False True Map.empty Map.empty
    mappend (DecClass x i1 r1 w1) (DecClass y i2 r2 w2) = DecClass (x || y) (i1 && i2) (Map.union r1 r2) (Map.union w1 w2)

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
isIterationStmtClass (StmtFallthru) = True
isIterationStmtClass c = False

hasStmtFallthru :: Set StmtClass -> Bool
hasStmtFallthru cs = not $ Set.null $ Set.filter isStmtFallthru cs

isStmtFallthru :: StmtClass -> Bool
isStmtFallthru (StmtFallthru) = True
isStmtFallthru c = False

data Typed a = Typed a Type
  deriving (Show,Data,Typeable,Functor,Eq,Ord,Generic)
instance Binary a => Binary (Typed a)
instance Hashable a => Hashable (Typed a)

instance PP m a => PP m (Typed a) where
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
isPublicType (BaseT b) = True
isPublicType (ComplexT (CType Public _ _)) = True
isPublicType _ = False

isPublicSecType :: SecType -> Bool
isPublicSecType Public = True
isPublicSecType _ = False

data ModuleTyVarId = ModuleTyVarId
    { modTyName :: (Identifier,TyVarId)
    , modTyId :: TyVarId
    }
  deriving (Eq,Ord,Data,Generic,Show)
instance Monad m => PP m ModuleTyVarId where
    pp (ModuleTyVarId (m,blk) i) = do
        ppm <- pp m
        ppblk <- pp blk
        ppi <- pp i
        return $ ppm <> char '.' <> ppblk <> char '.' <> ppi
instance Binary ModuleTyVarId
instance Hashable ModuleTyVarId

hashModuleTyVarId :: ModuleTyVarId -> Int
hashModuleTyVarId = hashWithSalt 0 . modTyId

instance (GenVar iden m,MonadIO m,IsScVar m iden) => Vars iden m ModuleTyVarId where
    traverseVars f x = return x

decTypeTyVarId :: DecType -> Maybe ModuleTyVarId
decTypeTyVarId (DecType i _ _ _ _ _ _ _ _) = Just i
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
type TIdentifier = Either SIdentifier PIdentifier

type SIdentifier = TypeName VarIdentifier ()

--ppStructAtt :: Attribute VarIdentifier Type -> Doc
--ppStructAtt (Attribute _ t n szs) = pp t <+> pp n

ppTpltArg :: PP m VarIdentifier => Constrained Var -> m Doc
ppTpltArg = ppConstrained ppTpltArg'
    where
    ppTpltArg' :: PP m VarIdentifier => Var -> m Doc
    ppTpltArg' (VarName BType v) = liftM (text "type" <+>) (pp v)
    ppTpltArg' (VarName (KType isPriv) k) = ppIsPrivate isPriv (liftM (text "kind" <+>) (pp k))
    ppTpltArg' (VarName (KindT k) v) = do
        ppv <- pp v
        ppk <- pp k
        return $ text "domain" <+> ppv <+> char ':' <+> ppk
    ppTpltArg' (VarName t v) | isIntType t = liftM (text "dim" <+>) (pp v)
    ppTpltArg' (VarName (VAType b sz) v) | isIntType b = liftM (text "dim..." <+>) (pp v)
    ppTpltArg' (VarName (VAType BType sz) v) = liftM (text "type..." <+>) (pp v)
    ppTpltArg' (VarName (VAType (KType isPriv) sz) v) = ppIsPrivate isPriv (liftM (text "kind..." <+>) (pp v))
    ppTpltArg' (VarName (VAType (KindT k) sz) v) = do
        ppv <- pp v
        ppk <- pp k
        return $ text "domain..." <+> ppv <+> ppk
    ppTpltArg' v = do
        ppv <- pp v
        ppl <- pp (loc v)
        error $ "ppTpltArg: " ++ show ppv ++ " " ++ show ppl
    
ppTSubsts :: PP m VarIdentifier => TSubsts -> m Doc
ppTSubsts xs = liftM vcat $ mapM ppSub $ Map.toList (unTSubsts xs)
    where
    ppSub (k,IdxT e) = do
        ppk <- pp k
        ppe <- ppExprTy e
        return $ ppk <+> char '=' <+> ppe
    ppSub (k,t) = do
        ppk <- pp k
        ppt <- pp t
        return $ ppk <+> char '=' <+> ppt

ppArrayRanges :: PP m VarIdentifier => [ArrayProj] -> m Doc
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
withoutImplicitClassify m = localOpts (\opts -> opts { implicitCoercions = False }) m

instance MonadIO m => GenVar VarIdentifier (TcM m) where
    genVar v = freshVarId (varIdBase v) (varIdPretty v)
    mkVar = return . mkVarId

--instance MonadIO m => GenVar VarIdentifier (SecrecM m) where
--    genVar v = freshVarIO v

instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m) => Vars VarIdentifier m VarIdentifier where
    traverseVars f n = do
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
    substL v | not (varIdTok v) = return $ Just v
    substL v = return Nothing

-- filter the constraints that depend on a set of variables
varsCstrGraph :: (VarsIdTcM m) => Set VarIdentifier -> IOCstrGraph -> TcM m IOCstrGraph
varsCstrGraph vs gr = labnfilterM aux (Graph.trc gr)
    where
    aux (i,x) = do
        xvs <- liftM Map.keysSet $ fvs (kCstr $ unLoc x)
        if Set.null (vs `Set.intersection` xvs)
            then return False
            else return True

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
    ast = StmtType $ Set.singleton StmtFallthru
assertStmt e = AssertStatement ast e
    where
    ast = StmtType $ Set.singleton StmtFallthru
    
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
debugTc m = do
    opts <- askOpts
    if debug opts then m else return ()

--instance (Vars iden (TcM m) a,MonadIO m) => Vars iden (TcM m) (IdRef ModuleTyVarId a) where
--    traverseVars f ref = do
--        x <- liftIO $ readIdRef ref
--        x' <- f x
--        i <- newModuleTyVarId
--        liftIO $ newIdRef i x'