{-# LANGUAGE Rank2Types, UndecidableInstances, DeriveFoldable, DeriveTraversable, FlexibleContexts, ConstraintKinds, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars

import Data.Foldable
import Data.IORef
import Data.Unique
import Data.Int
import Data.Word
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Generics hiding (GT,typeOf,typeRep)
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

import Control.Applicative
import Control.Monad.State as State
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding ((<>))
import Control.Monad.Trans.RWS (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS as RWS
import Control.Monad.Except
import Control.Monad.Trans.Control

import System.IO.Unsafe
import Unsafe.Coerce

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as Pretty

import qualified Data.HashTable.Weak.IO as WeakHash
import qualified System.Mem.Weak.Map as WeakMap
import System.Mem.Weak.Exts as Weak

-- warn for unused local variables

data IOCstr = IOCstr
    { kCstr :: TCstr
    , kStatus :: UniqRef TCstrStatus
    }
  deriving (Data,Typeable,Show)
  
instance Eq IOCstr where
    k1 == k2 = kStatus k1 == kStatus k2
instance Ord IOCstr where
    compare k1 k2 = compare (kStatus k1) (kStatus k2)

instance PP IOCstr where
    pp = pp . kCstr

data TCstrStatus
    = Unevaluated -- has never been evaluated
    | Evaluated ShowOrdDyn  -- has been evaluated
    | Erroneous -- has failed
        SecrecError -- failure error
  deriving (Data,Typeable,Show)

data Scope = GlobalScope | LocalScope
  deriving (Show,Read,Data,Typeable)

instance PP Scope where
    pp GlobalScope = text "global"
    pp LocalScope = text "local"

{-# NOINLINE globalEnv #-}
globalEnv :: IORef GlobalEnv
globalEnv = unsafePerformIO (newGlobalEnv >>= newIORef)

newGlobalEnv :: IO GlobalEnv
newGlobalEnv = do
    m <- WeakHash.newSized 1024
    return $ GlobalEnv m 0

resetGlobalEnv :: IO ()
resetGlobalEnv = do
--    g <- newGlobalEnv
--    writeIORef globalEnv g
    g <- readIORef globalEnv
    deps <- WeakHash.newSized 1024
    writeIORef globalEnv $ g { tDeps = deps }

orWarn :: (Monad m,Location loc) => TcM loc m a -> TcM loc m (Maybe a)
orWarn m = (liftM Just m) `catchError` \e -> do
    i <- getModuleCount
    TcM $ lift $ tell $ Map.singleton i $ ErrWarn e
    return Nothing

orWarn_ :: (Monad m,Location loc) => TcM loc m a -> TcM loc m ()
orWarn_ m = orWarn m >> return ()

data GlobalEnv = GlobalEnv
    { tDeps :: WeakHash.BasicHashTable VarIdentifier (WeakMap.WeakMap Unique IOCstr) -- variable dependencies
    , tyVarId :: TyVarId
    }

varIdDeps :: VarIdentifier -> IO (Set IOCstr)
varIdDeps v = do
    g <- readIORef globalEnv
    mb <- WeakHash.lookup (tDeps g) v
    case mb of
        Nothing -> return Set.empty
        Just cs -> WeakMap.foldM (\xs (_,iok) -> return $ Set.insert iok xs) Set.empty cs

type Hyps loc = Set (Loc loc IOCstr)

getModuleCount :: (Monad m) => TcM loc m Int
getModuleCount = liftM moduleCount State.get

data TcEnv loc = TcEnv {
      globalVars :: Map VarIdentifier (Bool,EntryEnv loc) -- ^ global variables: name |-> type of the variable
    , localVars  :: Map VarIdentifier (Bool,EntryEnv loc) -- ^ local variables: name |-> type of the variable
    , localFrees :: Set VarIdentifier -- ^ free internal const variables generated during typechecking
    , globalHyps :: Hyps loc -- ^ global hypotheses
    , localHyps :: Hyps loc -- ^ local hypotheses
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
    , tDict :: NeList (TDict loc) -- ^ A stack of dictionaries
    , openedCstrs :: Set IOCstr -- constraints being resolved, for dependency tracking
    , moduleCount :: Int
    }

tcEnvMap :: (loc2 -> loc1) -> (loc1 -> loc2) -> TcEnv loc2 -> TcEnv loc1
tcEnvMap f g env = TcEnv
    { globalVars = fmap (\(x,y) -> (x,fmap f y)) $ globalVars env
    , localVars = fmap (\(x,y) -> (x,fmap f y)) $ localVars env
    , localFrees = localFrees env
    , globalHyps = Set.fromList $ map (mapLoc f) $ Set.toList $ globalHyps env
    , localHyps = Set.fromList $ map (mapLoc f) $ Set.toList $ localHyps env
    , kinds = fmap (fmap f) $ kinds env
    , domains = fmap (fmap f) $ domains env
    , operators = Map.map (Map.map (fmap f)) $ operators env
    , procedures = Map.map (Map.map (fmap f)) $ procedures env
    , structs = Map.map (\(x,y) -> (fmap f x,Map.map (fmap f) y)) $ structs env
    , tDict = fmap (fmap f) $ tDict env
    , openedCstrs = openedCstrs env
    , moduleCount = moduleCount env
    }

type VarsId m a = Vars VarIdentifier m a
type VarsIdTcM loc m = (Typeable m,MonadIO m,MonadBaseControl IO m,VarsId (TcM loc m) loc,VarsId (TcM loc Symbolic) loc)

--insideTemplate :: TcM loc m Bool
--insideTemplate = liftM inTemplate State.get

emptyTcEnv :: TcEnv loc
emptyTcEnv = TcEnv Map.empty Map.empty Set.empty Set.empty Set.empty Map.empty Map.empty Map.empty Map.empty Map.empty (WrapNe mempty) Set.empty 0

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
varNameToType (VarName t n) | typeClass "varNameToType" t == TypeC = IdxT (RVariablePExpr t $ VarName t n)
varNameToType v = error $ "varNameToType " ++ show v

condVarNameToType :: Cond (VarName VarIdentifier Type) -> Type
condVarNameToType (Cond v c) = condType (varNameToType v) c

typeToVarName :: Type -> Maybe (VarName VarIdentifier Type)
typeToVarName (SecT (SVar n k)) = Just (VarName (SType k) n)
typeToVarName (ComplexT (CVar n)) = Just (VarName TType n)
typeToVarName (BaseT (BVar n)) = Just (VarName BType n)
typeToVarName (DecT (DVar n)) = Just (VarName DType n)
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

mapTcM :: (m (Either SecrecError ((a,TcEnv loc,()),SecrecWarnings)) -> n (Either SecrecError ((b,TcEnv loc,()),SecrecWarnings)))
    -> TcM loc m a -> TcM loc n b
mapTcM f (TcM m) = TcM $ RWS.mapRWST (mapSecrecM f) m

instance MonadTrans (TcM loc) where
    lift m = TcM $ lift $ SecrecM $ lift $ liftM (\x -> Right (x,Map.empty)) m

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
        then tcError (locpos l) $ ConstraintStackSizeExceeded (constraintStackSize opts)
        else TcM $ RWS.withRWST (\(i,f) s -> ((i + j,f . err),s)) m

tcPos :: (Monad m,Location loc) => TcM Position m a -> TcM loc m a
tcPos = tcLocM (locpos) (updpos noloc)

-- | Map different locations over @TcM@ monad.
tcLocM :: Monad m => (loc2 -> loc1) -> (loc1 -> loc2) -> TcM loc1 m a -> TcM loc2 m a
tcLocM f g m = do
    s2 <- get
    r2 <- ask
    (x,s1,w1) <- TcM $ lift $ runRWST (unTcM m) r2 (tcEnvMap f g s2)
    put (tcEnvMap g f s1)
    tell w1
    return x

-- | Enters a template declaration
--tcTemplateBlock :: TcM loc m a -> TcM loc m a
--tcTemplateBlock m = do
--    State.modify (\env -> env { inTemplate = True })
--    x <- m
--    State.modify (\env -> env { inTemplate = False })
--    return x

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: Monad m => TcM loc m a -> TcM loc m a
tcBlock m = do
    r <- ask
    s <- get
    (x,s',w') <- TcM $ lift $ runRWST (unTcM m) r s
    Writer.tell w'
    return x

execTcM :: (MonadIO m,Location loc) => TcM loc m a -> (Int,SecrecErrArr) -> TcEnv loc -> SecrecM m (a,TcEnv loc)
execTcM m arr env = do
    (x,env',()) <- RWS.runRWST (unTcM m) arr env
    return (x,env')

runTcM :: (MonadIO m,Location loc) => TcM loc m a -> SecrecM m a
runTcM m = liftM fst $ RWS.evalRWST (unTcM m) (0,id) emptyTcEnv

type PIdentifier = Either (ProcedureName VarIdentifier ()) (Op VarIdentifier Type)

-- | Does a constraint depend on global template, procedure or struct definitions?
isGlobalCstr :: TCstr -> Bool
isGlobalCstr = everything (||) (mkQ False isOverloadedK)
    where
    isOverloadedK (TDec {}) = True
    isOverloadedK (PDec {}) = True
    isOverloadedK (SupportedPrint {}) = True
    isOverloadedK _ = False

-- | A template constraint with a result type
data TcCstr
    = TDec -- ^ type template declaration
        (TypeName VarIdentifier ()) -- template name
        [Type] -- template arguments
        DecType -- result
    | TRet -- ^ template return type
        DecType -- template declaration
        Type -- result
    | PDec -- ^ procedure declaration
        PIdentifier -- procedure name
        (Maybe [Type]) -- template arguments
        [Expression VarIdentifier Type] -- procedure arguments
        Type -- return type
        DecType -- result
        (Maybe [VarName VarIdentifier Type]) -- resulting coerced procedure arguments
    | Equals Type Type -- ^ types equal
    | Coerces -- ^ types coercible
        (Expression VarIdentifier Type)
        Type
        (VarName VarIdentifier Type)
        Type
    | CoercesSec
        (Expression VarIdentifier Type) -- source expression
        ComplexType -- source complex type over which to perform classify
        (VarName VarIdentifier Type) -- target variable where to store the resulting expression
        SecType -- target security type
    | Coerces2 -- ^ bidirectional coercion
        (Expression VarIdentifier Type)
        Type
        (Expression VarIdentifier Type)
        Type
        (VarName VarIdentifier Type)
        (VarName VarIdentifier Type) 
        Type -- result
    | Coerces2Sec
        (Expression VarIdentifier Type)
        ComplexType -- base type 1
        (Expression VarIdentifier Type)
        ComplexType -- base type 2
        (VarName VarIdentifier Type) -- variable to store the 1st resulting expression
        (VarName VarIdentifier Type) -- variable to store the 2nd resulting expression
        SecType -- result
    | Unifies -- unification
        Type Type -- ^ type unification
    | SupportedPrint
        [Expression VarIdentifier Type] -- ^ can call tostring on the argument type
        [VarName VarIdentifier Type] -- resulting coerced procedure arguments
    | ProjectStruct -- ^ struct type projection
        BaseType (AttributeName VarIdentifier ()) 
        Type -- result
    | ProjectMatrix -- ^ matrix type projection
        ComplexType [ArrayProj]
        ComplexType -- result
    | IsReturnStmt (Set StmtClass) Type (ProcedureDeclaration VarIdentifier Position) -- ^ is return statement
    | MultipleSubstitutions VarIdentifier [(Type,[TcCstr])]
    | MatchTypeDimension
        ComplexType -- type
        Word64 -- expected dimension
  deriving (Data,Typeable,Show,Eq,Ord)
 
-- | checks (raise warnings)
data CheckCstr
    = CheckAssertion
        (SCond VarIdentifier Type) -- condition
    | CheckEqual -- x == y
        (SExpr VarIdentifier Type) -- left expr
        (SExpr VarIdentifier Type) -- right expr
    | CheckArrayAccess -- [min..max] in [0..size]
        ComplexType -- type
        Word64 -- dimension
        (SExpr VarIdentifier Type) -- min access
        (SExpr VarIdentifier Type) -- max access
        (SExpr VarIdentifier Type) -- array size
    | IsValid -- check if an index condition is valid (this is mandatory: raises an error)
        (ICond) -- condition
  deriving (Data,Typeable,Show,Eq,Ord)
 
-- hypothesis (raises warnings)
data HypCstr
    = HypCondition -- c == True
        (SExpr VarIdentifier Type)
    | HypNotCondition -- c == False
        (SExpr VarIdentifier Type)
    | HypAssign -- v == e
        (VarName VarIdentifier Type)
        (SExpr VarIdentifier Type)
    | HypEqual -- e1 == e2
        (SExpr VarIdentifier Type)
        (SExpr VarIdentifier Type)
  deriving (Data,Typeable,Show,Eq,Ord)
 
isTcCstr :: TCstr -> Bool
isTcCstr (TcK _) = True
isTcCstr (DelayedK k _) = isTcCstr k
isTcCstr (DepK _ k) = isTcCstr k
isTcCstr _ = False

isCheckCstr :: TCstr -> Bool
isCheckCstr (CheckK {}) = True
isCheckCstr (DelayedK k _) = isCheckCstr k
isCheckCstr (DepK _ k) = isCheckCstr k
isCheckCstr _ = False

data TCstr
    = TcK TcCstr
    | DelayedK
        TCstr -- a constraint
        (Int,SecrecErrArr) -- an error message with updated context
    | CheckK (Hyps Position) CheckCstr
    | HypK HypCstr
    | DepK (Set IOCstr) TCstr
  deriving (Data,Typeable,Show)
 
instance Eq TCstr where
    (DelayedK c1 _) == (DelayedK c2 _) = c1 == c2
    (TcK x) == (TcK y) = x == y
    (HypK x) == (HypK y) = x == y
    (CheckK hyps1 x) == (CheckK hyps2 y) = hyps1 == hyps2 && x == y
    (DepK xs1 k1) == (DepK xs2 k2) = k1 == k2
    x == y = False
    
instance Ord TCstr where
    compare (DelayedK c1 _) (DelayedK c2 _) = c1 `compare` c2
    compare (TcK c1) (TcK c2) = compare c1 c2
    compare (HypK x) (HypK y) = compare x y
    compare (CheckK hyps1 x) (CheckK hyps2 y) = mconcat [compare hyps1 hyps2,compare x y]
    compare (DepK _ k1) (DepK _ k2) = compare k1 k2
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)


ppExprTy e = pp e <+> text "::" <+> pp (loc e)

instance PP TcCstr where
    pp (TRet t x) = text "tret" <+> pp t <+> char '=' <+> pp x
    pp (TDec n ts x) = text "tdec" <+> pp n <+> sepBy space (map pp ts) <+> char '=' <+> pp x
    pp (PDec n specs ts r x Nothing) = pp r <+> pp n <+> abrackets (sepBy comma (map pp $ maybe [] id specs)) <+> parens (sepBy comma (map ppExprTy ts)) <+> char '=' <+> pp x
    pp (PDec n specs ts r x (Just xs)) = pp r <+> pp n <+> abrackets (sepBy comma (map pp $ maybe [] id specs)) <+> parens (sepBy comma (map ppExprTy ts)) <+> char '=' <+> pp x <+> parens (sepBy comma $ map pp xs)
    pp (Equals t1 t2) = text "equals" <+> pp t1 <+> pp t2
    pp (Coerces e1 t1 v2 t2) = text "coerces" <+> pp e1 <+> pp t1 <+> pp v2 <+> pp t2
    pp (CoercesSec e1 t1 v2 t2) = text "coercessec" <+> pp e1 <+> pp t1 <+> pp v2 <+> pp t2
    pp (Coerces2Sec e1 t1 e2 t2 v1 v2 x) = text "coerces2sec" <+> pp e1 <+> pp t1 <+> pp e2 <+> pp t2 <+> char '=' <+> pp v1 <+> pp v2 <+> pp x
    pp (Coerces2 e1 t1 e2 t2 v1 v2 x) = text "coerces2" <+> pp e1 <+> pp t1 <+> pp e2 <+> pp t2 <+> char '=' <+> pp v1 <+> pp v2 <+> pp x
    pp (Unifies t1 t2) = text "unifies" <+> pp t1 <+> pp t2
    pp (SupportedPrint ts xs) = text "print" <+> sepBy space (map pp ts) <+> sepBy space (map pp xs)
    pp (ProjectStruct t a x) = pp t <> char '.' <> pp a <+> char '=' <+> pp x
    pp (ProjectMatrix t as x) = pp t <> brackets (sepBy comma $ map pp as) <+> char '=' <+> pp x
    pp (IsReturnStmt cs t dec) = text "return" <+> (hcat $ map pp $ Set.toList cs) <+> pp t <+> pp dec
    pp (MultipleSubstitutions v s) = text "multiplesubstitutions" <+> pp v <+> pp (map fst s)
    pp (MatchTypeDimension t d) = text "matchtypedimension" <+> pp t <+> pp d

instance PP CheckCstr where
    pp (CheckAssertion c) = text "checkAssertion" <+> pp c
    pp (CheckEqual e1 e2) = text "checkEqual" <+> pp e1 <+> pp e2
    pp (CheckArrayAccess t d l u sz) = text "checkArrayAccess" <+> pp t <+> pp d <+> pp l <+> pp u <+> pp sz
    pp (IsValid c) = text "isvalid" <+> pp c

instance PP HypCstr where
    pp (HypCondition c) = pp c
    pp (HypNotCondition c) = char '!' <> pp c
    pp (HypAssign v e) = pp v <+> char '=' <+> pp e
    pp (HypEqual e1 e2) = pp e1 <+> text "==" <+> pp e2

instance PP TCstr where
    pp (DelayedK c f) = text "delayed" <+> pp c
    pp (TcK k) = pp k
    pp (CheckK hyps c) = sepBy (text "&&") (map pp $ Set.toList hyps) <+> text "=>" <+> pp c
    pp (HypK h) = pp h
    pp (DepK xs k) = parens (sepBy comma $ map pp $ Set.toList xs) <+> text "=>" <+> pp k

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
    
instance MonadIO m => Vars VarIdentifier m ArrayProj where
    traverseVars f (ArraySlice i1 i2) = do
        i1' <- f i1
        i2' <- f i2
        return $ ArraySlice i1' i2'
    traverseVars f (ArrayIdx w) = do
        w' <- f w
        return $ ArrayIdx w'
    
instance PP [Type] where
    pp xs = brackets $ sepBy comma $ map pp xs
    
instance MonadIO m => Vars VarIdentifier m [Type] where
    traverseVars f xs = mapM f xs
    
data ArrayIndex
    = NoArrayIndex
    | DynArrayIndex (SExpr VarIdentifier Type)
  deriving (Data,Typeable,Show)

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
    
instance MonadIO m => Vars VarIdentifier m ArrayIndex where
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

indexSExprLoc :: Location loc => Word64 -> SExpr iden (Typed loc)
indexSExprLoc i = (fmap (Typed noloc) $ indexExpr i)
    
instance MonadIO m => Vars VarIdentifier m TcCstr where
    traverseVars f (TRet t x) = do
        t' <- f t
        x' <- f x
        return $ TRet t' x'
    traverseVars f (TDec n args x) = do
        n' <- f n
        args' <- mapM f args
        x' <- f x
        return $ TDec n' args' x'
    traverseVars f (PDec n ts args ret x xs) = do
        n' <- f n
        x' <- f x
        ts' <- mapM f ts
        args' <- mapM f args
        ret' <- f ret
        xs' <- mapM (mapM f) xs
        return $ PDec n' ts' args' ret' x' xs'
    traverseVars f (Equals t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Equals t1' t2'
    traverseVars f (Coerces e1 t1 v2 t2) = do
        e1' <- f e1
        t1' <- f t1
        v2' <- f v2
        t2' <- f t2
        return $ Coerces e1' t1' v2' t2'
    traverseVars f (CoercesSec e1 t1 e2 t2) = do
        e1' <- f e1
        t1' <- f t1
        e2' <- f e2
        t2' <- f t2
        return $ CoercesSec e1' t1' e2' t2'
    traverseVars f (Coerces2 e1 t1 e2 t2 v1 v2 x) = do
        e1' <- f e1
        t1' <- f t1
        e2' <- f e2
        t2' <- f t2
        v1' <- f v1
        v2' <- f v2
        x' <- f x
        return $ Coerces2 e1' t1' e2' t2' v1' v2' x'
    traverseVars f (Coerces2Sec e1 t1 e2 t2 v1 v2 x) = do
        e1' <- f e1
        t1' <- f t1
        e2' <- f e2
        t2' <- f t2
        v1' <- f v1
        v2' <- f v2
        x' <- f x
        return $ Coerces2Sec e1' t1' e2' t2' v1' v2' x'
    traverseVars f (Unifies t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Unifies t1' t2'
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
    traverseVars f (IsReturnStmt cs t p) = do
        cs' <- mapSetM f cs
        t' <- f t
        p' <- f p
        return $ IsReturnStmt cs' t' p'
    traverseVars f (MultipleSubstitutions v s) = do
        v' <- f v
        s' <- mapM f s
        return $ MultipleSubstitutions v' s'
    traverseVars f (MatchTypeDimension t d) = do
        t' <- f t
        d' <- f d
        return $ MatchTypeDimension t' d'

instance MonadIO m => Vars VarIdentifier m CheckCstr where
    traverseVars f (CheckAssertion c) = do
        c' <- f c
        return $ CheckAssertion c'
    traverseVars f (CheckEqual c1 c2) = do
        c1' <- f c1
        c2' <- f c2
        return $ CheckEqual c1' c2'
    traverseVars f (CheckArrayAccess t d l u sz) = do
        t' <- f t
        d' <- f d
        l' <- f l
        u' <- f u
        sz' <- f sz
        return $ CheckArrayAccess t' d' l' u' sz'
    traverseVars f (IsValid c) = do
        c' <- f c
        return $ IsValid c'

instance MonadIO m => Vars VarIdentifier m HypCstr where
    traverseVars f (HypAssign v e) = do
        v' <- f v
        e' <- f e
        return $ HypAssign v' e'
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

instance MonadIO m => Vars VarIdentifier m TCstr where
    traverseVars f (DelayedK c err) = do
        c' <- f c
        return $ DelayedK c' err
    traverseVars f (TcK k) = do
        k' <- f k
        return $ TcK k'
    traverseVars f (CheckK hyps k) = do
        hyps' <- f hyps
        k' <- f k
        return $ CheckK hyps' k'
    traverseVars f (HypK k) = do
        k' <- f k
        return $ HypK k'
    traverseVars f (DepK xs k) = do
        xs' <- liftM Set.fromList $ mapM f $ Set.toList xs
        k' <- f k
        return $ DepK xs' k'

-- | Template constraint dictionary
-- a dictionary with a set of inferred constraints and resolved constraints
data TDict loc = TDict
    { tCstrs :: Map Unique (Loc loc IOCstr) -- a list of constraints
    , tChoices :: Set Unique -- set of choice constraints that have already been branched
    , tSubsts :: TSubsts -- variable substitions
    }
  deriving (Typeable,Eq,Data,Ord,Show)

-- | mappings from variables to current substitution
type TSubsts = Map VarIdentifier Type

instance Functor TDict where
    fmap f dict = dict { tCstrs = Map.map (mapLoc f) (tCstrs dict) }

instance Monoid (TDict loc) where
    mempty = TDict Map.empty Set.empty Map.empty
    mappend (TDict u1 c1 ss1) (TDict u2 c2 ss2) = TDict (Map.union u1 u2) (Set.union c1 c2) (ss1 `Map.union` ss2)

addCstrDeps :: (MonadIO m,VarsId m TCstr) => IOCstr -> m ()
addCstrDeps iok = do
    vs <- fvs (kCstr iok)
    g <- liftM tDeps $ liftIO $ readIORef globalEnv
    liftIO $ forM_ vs $ \v -> do
        mb <- WeakHash.lookup g v
        m <- maybe (WeakMap.new >>= \m -> WeakHash.insertWithMkWeak g v m (MkWeak $ mkWeakKey m) >> return m) return mb
        WeakMap.insertWithMkWeak m (uniqId $ kStatus iok) iok (MkWeak $ mkWeakKey $ kStatus iok)

instance (Location loc,MonadIO m,Vars VarIdentifier m loc) => Vars VarIdentifier m (TDict loc) where
    traverseVars f (TDict cstrs choices substs) = varsBlock $ do
        let cstrsLst = Map.toList cstrs
        cstrs' <- mapM (f . snd) $ cstrsLst
        let cstrs'' = map (\x -> (uniqId $ kStatus $ unLoc x,x)) cstrs'
        let keys = zip (map fst cstrsLst) (map fst cstrs'')
        let choices' = Set.map (\x -> maybe x id $ lookup x keys) choices
        lift $ mapM_ (addCstrDeps . unLoc . snd) cstrs''
        substs' <- liftM Map.fromList $ mapM (\(x,y) -> do { x' <- f x; y' <- f y; return (x',y') }) $ Map.toList substs
        return $ TDict (Map.fromList cstrs'') choices' substs'

instance (Vars VarIdentifier m loc,Vars VarIdentifier m a) => Vars VarIdentifier m (Loc loc a) where
    traverseVars f (Loc l a) = do
        l' <- f l
        a' <- f a
        return $ Loc l' a'

instance MonadIO m => Vars VarIdentifier m IOCstr where
    traverseVars f (IOCstr k ref) = do
        k' <- f k
        ref' <- liftIO $ readUniqRef ref >>= newUniqRef
        return $ IOCstr k' ref'

getTSubsts :: (Monad m,Location loc) => TcM loc m TSubsts
getTSubsts = do
    env <- State.get
    return $ tSubsts $ mconcatNe $ tDict env

ppTpltAppM :: (VarsIdTcM loc m,Location loc) => loc -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> TcM loc m Doc
ppTpltAppM l pid args es ret = do
    ss <- getTSubsts
    pid' <- substFromTSubsts l ss pid
    args' <- substFromTSubsts l ss args
    es' <- mapM (mapM (substFromTSubsts l ss)) es
    ret' <- substFromTSubsts l ss ret
    return $ ppTpltApp pid' args' es' ret'

specializeM :: (VarsId (TcM loc m) a,VarsIdTcM loc m,Location loc) => loc -> a -> TcM loc m a
specializeM l a = do
    ss <- getTSubsts
    substFromTSubsts l ss a

ppM :: (VarsId (TcM loc m) a,VarsIdTcM loc m,PP a,Location loc) => loc -> a -> TcM loc m Doc
ppM l a = liftM pp $ specializeM l a

substFromTDict :: (VarsIdTcM loc m,Location loc,VarsId (TcM loc m) a) => loc -> TDict loc -> a -> TcM loc m a
substFromTDict l dict = substFromTSubsts l (tSubsts dict)

substFromTSubsts :: (VarsIdTcM loc m,Location loc,VarsId (TcM loc m) a) => loc -> TSubsts -> a -> TcM loc m a
substFromTSubsts l tys = substProxy (substsFromTSubsts l tys)
    
substsFromTSubsts :: (Typeable loc,Monad m) => loc -> TSubsts -> SubstsProxy VarIdentifier (TcM loc m)
substsFromTSubsts (l::loc) tys = \proxy x -> do
    case Map.lookup x tys of
        Nothing -> return Nothing
        Just ty -> case proxy of
            (eq (typeRep :: TypeOf (VarName VarIdentifier Type)) -> EqT) ->
                return $ typeToVarName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier Type)) -> EqT) ->
                return $ typeToDomainName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier ())) -> EqT) ->
                return $ fmap funit $ typeToDomainName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToDomainName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier Type)) -> EqT) ->
                return $ typeToTypeName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier ())) -> EqT) ->
                return $ fmap funit $ typeToTypeName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToTypeName ty
            (eq (typeRep :: TypeOf SecType) -> EqT) ->
                case ty of
                    SecT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf ComplexType) -> EqT) ->
                case ty of
                    ComplexT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf BaseType) -> EqT) ->
                case ty of
                    BaseT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (Expression VarIdentifier Type)) -> EqT) ->
                case ty of
                    IdxT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (Expression VarIdentifier (Typed loc))) -> EqT) ->
                case ty of
                    IdxT s -> return $ Just $ fmap (Typed l) s
                    otherwise -> return Nothing
            otherwise -> return Nothing
  where
    eq x proxy = eqTypeOf x (typeOfProxy proxy)

instance PP (TDict loc) where
    pp dict = text "Constraints:" $+$ nest 4 (vcat $ map pp $ Map.elems $ tCstrs dict)
          $+$ text "Substitutions:" $+$ nest 4 (ppTSubsts (tSubsts dict))

ppConstraints :: MonadIO m => TDict loc -> TcM loc m Doc
ppConstraints d = do
    let ppK (Loc l c) = do
        s <- liftIO $ readUniqRef $ kStatus c
        let pre = pp (kCstr c) <+> text (show $ hashUnique $ uniqId $ kStatus c)
        case s of
            Evaluated t -> return $ pre <+> text (show t)
            Unevaluated -> return $ pre
            Erroneous err -> return $ pre <> char '=' <+> if isHaltError err then text "HALT" else text "ERROR"
    ss <- liftM vcat $ mapM ppK (Map.elems $ tCstrs d)
    return ss

data VarIdentifier = VarIdentifier
        { varIdBase :: Identifier
        , varIdUniq :: Maybe TyVarId
        , varIdTok :: Bool -- if the variable is a token (not to be resolved) (only used for comparisons)
        }
    deriving (Typeable,Data,Show)

instance Eq VarIdentifier where
    v1 == v2 = varIdBase v1 == varIdBase v2 && varIdUniq v1 == varIdUniq v2
instance Ord VarIdentifier where
    compare v1 v2 = mconcat [varIdBase v1 `compare` varIdBase v2,varIdUniq v1 `compare` varIdUniq v2]

varTok :: VarName VarIdentifier loc -> Bool
varTok (VarName _ n) = varIdTok n

mkVarId :: Identifier -> VarIdentifier
mkVarId s = VarIdentifier s Nothing False

instance PP VarIdentifier where
    pp = ppVarId

type TyVarId = Int

data SecType
    = Public -- ^ public domain
    | Private -- ^ private domain
        (DomainName VarIdentifier ()) -- ^ domain
        (KindName VarIdentifier ()) -- ^ kind
    | SVar VarIdentifier SVarKind
  deriving (Typeable,Show,Data,Eq,Ord)

data SVarKind
    = AnyKind
    | PrivateKind (Maybe (KindName VarIdentifier ()))
  deriving (Typeable,Show,Data,Eq,Ord)

data DecType
    = ProcType -- ^ procedure type
        TyVarId -- ^ unique procedure declaration id
        Position
        PIdentifier
        [(Bool,Cond (VarName VarIdentifier Type))] -- typed procedure arguments
        Type -- return type
        [Statement VarIdentifier (Typed Position)] -- ^ the procedure's body
    | StructType -- ^ Struct type
            TyVarId -- ^ unique structure declaration id
            Position -- ^ location of the procedure declaration
            SIdentifier
            [Cond (Attribute VarIdentifier Type)] -- ^ typed arguments
    | TpltType -- ^ Template type
            TyVarId -- ^ unique template declaration id
            [Cond (VarName VarIdentifier Type)] -- ^ template variables
            (TDict Position) -- ^ template constraints depending on the variables
            [Type] -- ^ template specializations
            (Set VarIdentifier) -- set of free internal constant variables generated when typechecking the template
            DecType -- ^ template's type
    | DVar -- declaration variable
        VarIdentifier
  deriving (Typeable,Show,Data)

instance Eq DecType where
    (DVar v1) == (DVar v2) = v1 == v2
    x == y = decTypeTyVarId x == decTypeTyVarId y
instance Ord DecType where
    compare (DVar v1) (DVar v2) = compare v1 v2
    compare x y = compare (decTypeTyVarId x) (decTypeTyVarId y)

data Cond a = Cond a (Maybe (SCond VarIdentifier Type))
  deriving (Typeable,Show,Data,Eq,Ord,Functor)

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
        e' <- f e
        return $ Cond t' e'

data BaseType
    = TyPrim Prim
    | TyDec DecType
    | BVar VarIdentifier
  deriving (Typeable,Show,Data,Eq,Ord)

type SExpr iden loc = (Expression iden loc)
type SCond iden loc = (Expression iden loc)

data ComplexType
    = CType -- ^ Compound SecreC type
        SecType -- ^ security type
        BaseType -- ^ data type
        (SExpr VarIdentifier Type) -- ^ dimension (default = 0, i.e., scalars)
        [SExpr VarIdentifier Type] -- ^ sizes for each dimension (dependent types?) -- NOTE: check bounds if size is statically known?
    | CVar VarIdentifier
    | Void -- ^ Empty type
    | TyLit -- ^ the most concrete type for a literal. a complex type because we may cast literals into arrays
           (Literal ()) -- ^ the literal itself
    | ArrayLit -- ^ a concrete array
        (NeList (SExpr VarIdentifier Type))
  deriving (Typeable,Show,Data,Eq,Ord)

data SysType
    = SysPush Type
    | SysRet Type
    | SysRef Type
    | SysCRef Type
  deriving (Typeable,Show,Data,Eq,Ord)

data Type
    = NoType String -- ^ For locations with no associated type information
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
    | IdxT (SExpr VarIdentifier Type) -- for index expressions
    | CondType Type (SCond VarIdentifier Type) -- a type with an invariant
  deriving (Typeable,Show,Data,Eq,Ord)

condType :: Type -> Maybe (SCond VarIdentifier Type) -> Type
condType t Nothing = t
condType t (Just c) = CondType t c

instance PP SecType where
    pp Public = text "public"
    pp (Private d k) = pp d
    pp (SVar v k) = parens (ppVarId v <+> text "::" <+> pp k)
instance PP DecType where
    pp (TpltType _ vars dict specs frees body@(StructType _ _ n atts)) = pp dict <+> text "=>" $+$
            text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
        $+$ text "struct" <+> pp n <> abrackets (sepBy comma $ map pp specs) <+> braces (text "...")
    pp (TpltType _ vars dict [] frees body@(ProcType _ _ (Left n) args ret stmts)) = pp dict <+> text "=>" $+$
            text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
        $+$ pp ret <+> pp n <> parens (sepBy comma $ map (\(isCond,Cond (VarName t n) c) -> ppConst isCond <+> pp t <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (TpltType _ vars dict [] frees body@(ProcType _ _ (Right n) args ret stmts)) = pp dict <+> text "=>" $+$
            text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
        $+$ pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(isCond,Cond (VarName t n) c) -> ppConst isCond <+> pp t <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (ProcType _ _ (Left n) args ret stmts) =
            pp ret <+> pp n <> parens (sepBy comma $ map (\(isCond,Cond (VarName t n) c) -> ppConst isCond <+> pp t <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (ProcType _ _ (Right n) args ret stmts) =
            pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(isCond,Cond (VarName t n) c) -> ppConst isCond <+> pp t <+> pp n <+> ppOpt c (braces . pp)) args) <+> braces (pp stmts)
    pp (DVar v) = pp v
    pp (StructType _ _ n atts) = text "struct" <+> pp n <+> braces (text "...")
    pp d = error $ "pp: " ++ show d
instance PP BaseType where
    pp (TyPrim p) = pp p
    pp (TyDec d) = pp d
    pp (BVar v) = ppVarId v
instance PP ComplexType where
    pp (TyLit lit) = pp lit
    pp (ArrayLit es) = braces (sepBy comma $ map pp $ Foldable.toList es)
    pp Void = text "void"
    pp (CType s t d szs) = pp s <+> pp t <> brackets (brackets (pp d)) <> parens (sepBy comma $ map pp szs)
    pp (CVar v) = ppVarId v
instance PP SysType where
    pp t@(SysPush {}) = text (show t)
    pp t@(SysRet {}) = text (show t)
    pp t@(SysRef {}) = text (show t)
    pp t@(SysCRef {}) = text (show t)

instance PP Type where
    pp t@(NoType msg) = text "no type"
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
    pp (CondType t c) = ppCond pp (Cond t $ Just c)

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

instance PP TypeClass where
    pp KindStarC = text "kind star"
    pp KindC = text "kind"
    pp DomainC = text "domain"
    pp TypeStarC = text "type star"
    pp ExprC = text "index expression"
    pp TypeC = text "complex type"
    pp SysC = text "system call parameter"
    pp DecC = text "declaration"
    

typeClass :: String -> Type -> TypeClass
typeClass msg (CondType t _) = typeClass msg t
typeClass msg TType = TypeStarC
typeClass msg BType = TypeStarC
typeClass msg KType = KindStarC
typeClass msg (SType _) = KindC
typeClass msg (SecT _) = DomainC
typeClass msg (DecT _) = DecC
typeClass msg (SysT _) = SysC
typeClass msg (IdxT _) = ExprC
typeClass msg (ComplexT _) = TypeC
typeClass msg (BaseT _) = TypeC
typeClass msg t = error $ msg ++ ": no typeclass for " ++ show t

isStruct :: DecType -> Bool
isStruct (TpltType _ _ _ _ _ (StructType {})) = True
isStruct (StructType {}) = True
isStruct _ = False

isStructTemplate :: Type -> Bool
isStructTemplate (DecT (TpltType _ _ _ _ _ (StructType {}))) = True
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

instance Monad m => Vars VarIdentifier m StmtClass where
    traverseVars f c = return c
  
instance Monad m => Vars VarIdentifier m SecType where
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

instance MonadIO m => Vars VarIdentifier m [TCstr] where
    traverseVars f xs = mapM f xs
    
instance MonadIO m => Vars VarIdentifier m [TcCstr] where
    traverseVars f xs = mapM f xs

instance PP [TCstr] where
    pp xs = brackets (sepBy comma $ map pp xs)
    
instance PP [TcCstr] where
    pp xs = brackets (sepBy comma $ map pp xs)

instance MonadIO m => Vars VarIdentifier m DecType where
    traverseVars f (ProcType pid p n vs t stmts) = varsBlock $ do
        n' <- f n
        vs' <- inLHS $ mapM f vs
        t' <- f t
        stmts' <- f stmts
        return $ ProcType pid p n' vs' t' stmts'
    traverseVars f (StructType tid p n as) = varsBlock $ do
        n' <- f n
        as' <- inLHS $ mapM f as
        return $ StructType tid p n' as'
    traverseVars f (TpltType tid vs d spes frees t) = varsBlock $ do
        vs' <- inLHS $ mapM f vs
        frees' <- inLHS $ liftM Set.fromList $ mapM f $ Set.toList frees
        d' <- f d
        spes' <- mapM f spes
        t' <- f t
        return $ TpltType tid vs' d' spes' frees' t'
    traverseVars f (DVar v) = do
        v' <- f v
        return $ DVar v'
    substL (DVar v) = return $ Just v
    substL _ = return Nothing
    
instance MonadIO m => Vars VarIdentifier m BaseType where
    traverseVars f (TyPrim p) = do
        p' <- f p
        return $ TyPrim p'
    traverseVars f (TyDec d) = do
        d' <- f d
        return $ TyDec d'
    traverseVars f (BVar v) = do
        v' <- f v
        return $ BVar v'
    substL (BVar v) = return $ Just v
    substL e = return Nothing
 
instance MonadIO m => Vars VarIdentifier m ComplexType where
    traverseVars f (TyLit l) = do
        l' <- f l
        return $ TyLit l'
    traverseVars f (ArrayLit l) = do
        l' <- mapM f l
        return $ ArrayLit l'
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
    substL (CVar v) = return $ Just v
    substL e = return Nothing

instance MonadIO m => Vars VarIdentifier m SysType where
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

instance Monad m => Vars VarIdentifier m SVarKind where
    traverseVars f AnyKind = return AnyKind
    traverseVars f (PrivateKind k) = do
        k' <- f k
        return $ PrivateKind k'

secTypeKind :: SecType -> SVarKind
secTypeKind Public = AnyKind
secTypeKind (Private _ k) = PrivateKind $ Just k
secTypeKind (SVar v k) = k

instance PP SVarKind where
    pp AnyKind = text "*"
    pp (PrivateKind Nothing) = text "private *"
    pp (PrivateKind (Just k)) = text "private" <+> pp k
    
instance MonadIO m => Vars VarIdentifier m Type where
    traverseVars f (NoType x) = return (NoType x)
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
    traverseVars f (CondType t c) = do
        t' <- f t
        c' <- f c
        return $ CondType t' c'
    substL (BaseT (BVar v)) = return $ Just v
    substL (SecT (SVar v _)) = return $ Just v
    substL (ComplexT (CVar v)) = return $ Just v
    substL (DecT (DVar v)) = return $ Just v
    substL (IdxT (RVariablePExpr _ v)) = return $ Just $ varNameId v
    substL e = return Nothing

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
decTypeTyVarId (StructType i _ _ _) = Just i
decTypeTyVarId (ProcType i _ _ _ _ _) = Just i
decTypeTyVarId (TpltType i _ _ _ _ _) = Just i
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

setBase b (CType s t d sz) = CType s b d sz

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
    ppTpltArg' (VarName BType v) = text "type" <+> ppVarId v
    ppTpltArg' (VarName TType v) = text "type" <+> ppVarId v
    ppTpltArg' (VarName (SType AnyKind) v) = text "domain" <+> ppVarId v
    ppTpltArg' (VarName (SType (PrivateKind Nothing)) v) = text "domain" <+> ppVarId v
    ppTpltArg' (VarName (SType (PrivateKind (Just k))) v) = text "domain" <+> ppVarId v <+> char ':' <+> pp k
    ppTpltArg' (VarName t v) | isIntType t = text "dim" <+> ppVarId v

ppVarId :: VarIdentifier -> Doc
ppVarId (VarIdentifier n Nothing _) = text n
ppVarId (VarIdentifier n (Just i) _) = text n <> char '_' <> Pretty.int i

ppTpltApp :: TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> Doc
ppTpltApp (Left n) args Nothing Nothing = text "struct" <+> pp n <> abrackets (sepBy comma $ map pp $ concat $ args)
ppTpltApp (Right (Left n)) targs args (Just ret) = pp ret <+> pp n <> abrackets (sepBy comma $ map pp $ concat targs) <> parens (sepBy comma $ map (\e -> pp e <+> text "::" <+> pp (loc e)) $ concat args)
ppTpltApp (Right (Right n)) targs args (Just ret) = pp ret <+> pp n <> abrackets (sepBy comma $ map pp $ concat targs) <> parens (sepBy comma $ map (\e -> pp e <+> text "::" <+> pp (loc e)) $ concat args)
    
ppTSubsts :: TSubsts -> Doc
ppTSubsts xs = vcat $ map ppSub $ Map.toList xs
    where
    ppSub (k,t) = ppVarId k <+> char '=' <+> pp t

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
    HsLit :: Literal () -> HsVal
    HsContinue :: HsVal
    HsBreak :: HsVal
    HsVoid :: HsVal
    HsSysPush :: HsVal -> HsVal
    HsSysRet :: HsVal -> HsVal
    HsSysRef :: HsVal -> HsVal
    HsSysCRef :: HsVal -> HsVal
  deriving (Data,Typeable,Show)

--instance Monad m => Vars m HsVal where
--    traverseVars f h = return h

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

bytes :: ComplexType
bytes = CType Public (TyPrim $ DatatypeUint8 ()) (indexSExpr 1) []
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
defCType t = CType Public t (indexSExpr 0) []

instance Hashable VarIdentifier where
    hashWithSalt i v = hashWithSalt (maybe i (i+) $ varIdUniq v) (varIdBase v)

type Prim = PrimitiveDatatype ()

-- * Index expressions
-- | Index expressions. Normal form: ...
data IExpr
    -- | Integer literals
    = IInt !Integer
    -- | Index variables
    | IIdx (VarName VarIdentifier Prim)
    -- | Arithmetic sum
    | ISum [IExpr]
    -- | Binary arithmetic operators
    | IArith IAOp (IExpr) (IExpr)
    -- | Symmetric
    | ISym (IExpr)
  deriving (Eq, Ord, Show, Data, Typeable)
  
instance PP IExpr where
    pp (IInt n)            = integer n
    pp (IIdx (VarName t v)) = pp v <+> text "::" <+> pp t
    pp (ISum l)            = parens (cat (punctuate (text " + ") (map pp l)))
    pp ctx@(IArith op l r) = parens (pp l) <+> pp op <+> parens (pp r)
    pp ctx@(ISym e)        = parens $ char '-' <> parens (pp e)
  
-- * Index conditions
-- TODO: Implication to decide validity?
-- | The conditions are expressed as boolean values and expressions over them.
data ICond
    -- | Boolean literal
    = IBool !Bool
    -- | Boolean variable
    | IBInd VarIdentifier
    -- | Boolean negation (not)
    | INot (ICond)
    -- | Boolean conjunction. The list must be non-empty.
    | IAnd [ICond]
    -- | Boolean binary operations.
    | IBoolOp IBOp (ICond) (ICond)
    -- | Non-negative operator on expressions. 
    -- This has the meaning of @0 <= expr@
    | ILeq (IExpr)
    -- | Test of equality with 0 (@expr == 0@).
    | IEq (IExpr)
    deriving (Eq, Ord, Show, Data, Typeable)

instance PP ICond where
    pp (IBool b) = text $ show b
    pp (IBInd v) = pp v <+> text "::" <+> pp bool
    pp ctx@(INot e) = char '!' <> parens (pp e)
    pp (IAnd l) = parens (cat (punctuate (text " && ") (map pp l)))
    pp ctx@(IBoolOp op l r) = parens (pp l) <+> pp op <+> parens (pp r)
    pp ctx@(ILeq r) = integer 0 <+> text "<=" <+> parens (pp r)
    pp ctx@(IEq r) = integer 0 <+> text "="  <+> parens (pp r)

-- | Boolean binary operations
data IBOp 
    = IOr  -- ^ Boolean disjunction
    | IXor -- ^ Boolean exclusive disjunction
    deriving (Eq, Ord, Read, Show, Data, Typeable)

instance PP IBOp where
    pp IOr  = text "||"
    pp IXor = text "^^"

-- | Binary arithmetic operators
data IAOp 
    = IMinus -- ^ Substraction
    | ITimes -- ^ Multiplication
    | IPower -- ^ Exponentiation
    | IDiv   -- ^ Whole division
    | IModOp -- ^ Remainer of whole division
    deriving (Eq, Ord, Read, Show, Data, Typeable)

instance (Monad m) => Vars VarIdentifier m (IExpr) where
    traverseVars f (IInt i) = liftM IInt $ f i
    traverseVars f (IIdx v) = do
        v' <- f v
        return $ IIdx v
    traverseVars f (ISum is) = liftM ISum $ mapM f is
    traverseVars f (IArith o e1 e2) = do
        o' <- f o
        e1' <- f e1
        e2' <- f e2
        return $ IArith o' e1' e2'
    traverseVars f (ISym e) = liftM ISym $ f e
    substL (IIdx (VarName _ n)) = return $ Just n
    substL _ = return Nothing
instance (Monad m) => Vars VarIdentifier m (ICond) where
    traverseVars f (IBool b) = liftM IBool $ f b
    traverseVars f (IBInd n) = do
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        return $ IBInd n
    traverseVars f (INot c) = liftM INot $ f c
    traverseVars f (IAnd cs) = liftM IAnd $ mapM f cs
    traverseVars f (IBoolOp o c1 c2) = do
        o' <- f o
        c1' <- f c1
        c2' <- f c2
        return $ IBoolOp o' c1' c2'
    traverseVars f (ILeq e) = liftM ILeq $ f e
    traverseVars f (IEq e) = liftM IEq $ f e
    substL (IBInd n) = return $ Just n
    substL _ = return Nothing
instance (IsScVar iden,Monad m) => Vars iden m IBOp where
    traverseVars f o = return o
instance (IsScVar iden,Monad m) => Vars iden m IAOp where
    traverseVars f o = return o

instance PP IAOp where
    pp IMinus = char '-'
    pp ITimes = char '*'
    pp IPower = text "**"
    pp IDiv   = char '/'
    pp IModOp = char '%'

tcError :: (MonadIO m,Location loc) => Position -> TypecheckerErr -> TcM loc m a
tcError pos msg = throwTcError $ TypecheckerError pos msg  

genTcError :: (MonadIO m,Location loc) => Position -> Doc -> TcM loc m a
genTcError pos msg = throwTcError $ GenericError pos msg  

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
    
varExpr :: Location loc => VarName iden loc -> Expression iden loc
varExpr v = RVariablePExpr (loc v) v

varIdxT :: VarName VarIdentifier Type -> Type
varIdxT v = IdxT $ varExpr v

askOpts :: Monad m => TcM loc m Options
askOpts = TcM $ lift ask

localOpts :: Monad m => (Options -> Options) -> TcM loc m a -> TcM loc m a
localOpts f (TcM m) = TcM $ RWS.mapRWST (SecrecM . Reader.local f . unSecrecM) m

withoutImplicitClassify :: Monad m => TcM loc m a -> TcM loc m a
withoutImplicitClassify m = localOpts (\opts -> opts { implicitClassify = False }) m

instance Monad m => Vars VarIdentifier m VarIdentifier where
    traverseVars f n = do
        isLHS <- getLHS
        if isLHS then addBV n else addFV n
        return n
    substL v = return $ Just v
    
    