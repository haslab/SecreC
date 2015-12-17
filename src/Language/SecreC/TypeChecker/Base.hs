{-# LANGUAGE FlexibleContexts, ConstraintKinds, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars

import Data.IORef
import Data.Unique
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
import Data.Hashable

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

import qualified Data.HashTable.Weak.IO as WeakHash
import qualified System.Mem.Weak.Map as WeakMap
import System.Mem.Weak.Exts as Weak

-- warn for unused local variables

data Scope = GlobalScope | LocalScope
  deriving (Show,Read,Data,Typeable)

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

data GlobalEnv = GlobalEnv
    { tDeps :: WeakHash.BasicHashTable VarIdentifier (WeakMap.WeakMap Unique (UniqRef TCstrStatus)) -- variable dependencies
    , tyVarId :: TyVarId
    }

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
--    , inTemplate :: Bool -- ^ @True@ if we are type checking the body of a template declaration
    , tDict :: NeList (TDict loc) -- ^ A stack of dictionaries
    , openedCstrs :: Set IOCstr -- constraints being resolved, for dependency tracking
    }
  deriving Functor

type VarsTcM loc = Vars (TcM loc) loc

--insideTemplate :: TcM loc Bool
--insideTemplate = liftM inTemplate State.get

emptyTcEnv :: TcEnv loc
emptyTcEnv = TcEnv Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty (WrapNe mempty) Set.empty

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

instance (MonadIO m,Location loc,Vars m loc) => Vars m (EntryValue loc) where
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
varNameToType (VarName DType n) = DecT $ DVar $ VarName () n
varNameToType (VarName t n) | isIntType t = IdxT $ RVariablePExpr t $ VarName t n 

typeToVarName :: Type -> Maybe (VarName VarIdentifier Type)
typeToVarName (SecT (SVar (VarName () n) k)) = Just (VarName (SType k) n)
typeToVarName (ComplexT (CVar (VarName () n))) = Just (VarName TType n)
typeToVarName (BaseT (BVar (VarName () n))) = Just (VarName BType n)
typeToVarName (DecT (DVar (VarName () n))) = Just (VarName DType n)
typeToVarName (IdxT (RVariablePExpr _ (VarName t n))) | isIntType t = Just (VarName t n)
typeToVarName _ = Nothing

type SecrecErrArr = SecrecError -> SecrecError

newtype TcM loc a = TcM { unTcM :: RWST SecrecErrArr () (TcEnv loc) SecrecM a }
    deriving (Functor,Applicative,Typeable,Monad,MonadIO,MonadState (TcEnv loc),MonadReader SecrecErrArr,MonadWriter (),MonadError SecrecError,MonadPlus,Alternative)

tcError :: Position -> TypecheckerErr -> TcM loc a
tcError pos msg = do
    f <- Reader.ask
    let err = f $ typecheckerError pos msg
    ios <- liftM openedCstrs State.get
    let add io = liftIO $ writeUniqRef (kStatus io) (Erroneous err)
    mapM_ add ios
    throwError err

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
--tcTemplateBlock :: TcM loc a -> TcM loc a
--tcTemplateBlock m = do
--    State.modify (\env -> env { inTemplate = True })
--    x <- m
--    State.modify (\env -> env { inTemplate = False })
--    return x

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: TcM loc a -> TcM loc a
tcBlock m = do
    r <- ask
    s <- get
    (x,s',w') <- TcM $ lift $ runRWST (unTcM m) r s
    Writer.tell w'
    return x

runTcM :: Location loc => TcM loc a -> SecrecM a
runTcM m = liftM fst $ RWS.evalRWST (unTcM m) id emptyTcEnv

type PIdentifier = Either (ProcedureName VarIdentifier ()) (Op VarIdentifier Type)

-- | A template constraint with a result type
data TCstr
    = TDec -- ^ type template declaration
        (TypeName VarIdentifier ()) -- template name
        [Type] -- template arguments
        DecType -- result
    | TRet -- ^ template return type
        DecType -- template declaration
        Type -- result
    | PDec -- ^ procedure declaration
        PIdentifier -- procedure name
        [Type] -- procedure arguments
        Type -- return type
        DecType -- result
    | Equals Type Type -- ^ types equal
    | Coerces Type Type -- ^ types coercible
    | CoercesSec
        SecType -- security type
        SecType -- security type
        ComplexType -- complex type over which to perform classify
    | Coerces2 -- ^ bidirectional coercion
        Type Type 
        Type -- result
    | Coerces2Sec
        SecType -- security type
        SecType -- security type
        ComplexType -- complex type over which to perform classify
        SecType -- result
    | Unifies Type Type -- ^ type unification
    | SupportedPrint [Type] -- ^ can call tostring on the argument type
    | ProjectStruct -- ^ struct type projection
        DecType (AttributeName VarIdentifier ()) 
        Type -- result
    | ProjectMatrix -- ^ matrix type projection
        ComplexType [ArrayProj]
        ComplexType -- result
    | IsReturnStmt (Set StmtClass) Type (ProcedureDeclaration VarIdentifier Position) -- ^ is return statement
    | DelayedCstr
        TCstr -- a constraint
        (SecrecError -> SecrecError) -- an error message with updated context
    | MultipleSubstitutions (VarName VarIdentifier ()) [(Type,[TCstr])]
  deriving (Data,Typeable,Show)
  
instance Eq TCstr where
    (TRet x1 r1) == (TRet x2 r2) = x1 == x2 && r1 == r2
    (TDec n1 ts1 r1) == (TDec n2 ts2 r2) = n1 == n2 && ts1 == ts2 && r1 == r2
    (PDec n1 ts1 r1 x1) == (PDec n2 ts2 r2 x2) = n1 == n2 && ts1 == ts2 && r1 == r2 && x1 == x2
    (Equals x1 y1) == (Equals x2 y2) = x1 == x2 && y1 == y2
    (Coerces x1 y1) == (Coerces x2 y2) = x1 == x2 && y1 == y2
    (CoercesSec x1 y1 c1) == (CoercesSec x2 y2 c2) = x1 == x2 && y1 == y2 && c1 == c2
    (Coerces2Sec x1 y1 c1 r1) == (Coerces2Sec x2 y2 c2 r2) = x1 == x2 && y1 == y2 && c1 == c2 && r1 == r2
    (Coerces2 x1 y1 r1) == (Coerces2 x2 y2 r2) = x1 == x2 && y1 == y2 && r1 == r2
    (Unifies x1 y1) == (Unifies x2 y2) = x1 == x2 && y1 == y2
    (SupportedPrint x1) == (SupportedPrint x2) = x1 == x2
    (ProjectStruct x1 y1 r1) == (ProjectStruct x2 y2 r2) = x1 == x2 && y1 == y2 && r1 == r2
    (ProjectMatrix x1 y1 r1) == (ProjectMatrix x2 y2 r2) = x1 == x2 && y1 == y2 && r1 == r2
    (IsReturnStmt s1 x1 y1) == (IsReturnStmt s2 x2 y2) = x1 == x2 && y1 == y2
    (DelayedCstr c1 _) == (DelayedCstr c2 _) = c1 == c2
    (MultipleSubstitutions v1 s1) == (MultipleSubstitutions v2 s2) = v1 == v2 && s1 == s2
    x == y = False
    
instance Ord TCstr where
    compare (TRet x1 r1) (TRet x2 r2) = mconcat [compare x1 x2,compare r1 r2]
    compare (TDec n1 ts1 r1) (TDec n2 ts2 r2) = mconcat [n1 `compare` n2,ts1 `compare` ts2,r1 `compare` r2]
    compare (PDec n1 ts1 r1 res1) (PDec n2 ts2 r2 res2) = mconcat [n1 `compare` n2,ts1 `compare` ts2,r1 `compare` r2,res1 `compare` res2]
    compare (Equals x1 y1) (Equals x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (Coerces x1 y1) (Coerces x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (CoercesSec x1 y1 c1) (CoercesSec x2 y2 c2) = mconcat [x1 `compare` x2,y1 `compare` y2,c1 `compare` c2]
    compare (Coerces2Sec x1 y1 c1 r1) (Coerces2Sec x2 y2 c2 r2) = mconcat [x1 `compare` x2,y1 `compare` y2,c1 `compare` c2,r1 `compare` r2]
    compare (Coerces2 x1 y1 r1) (Coerces2 x2 y2 r2) = mconcat [x1 `compare` x2,y1 `compare` y2,r1 `compare` r2]
    compare (Unifies x1 y1) (Unifies x2 y2) = mconcat [x1 `compare` x2,y1 `compare` y2]
    compare (SupportedPrint x1) (SupportedPrint x2) = x1 `compare` x2
    compare (ProjectStruct x1 y1 r1) (ProjectStruct x2 y2 r2) = mconcat [x1 `compare` x2,y1 `compare` y2,r1 `compare` r2]
    compare (ProjectMatrix x1 y1 r1) (ProjectMatrix x2 y2 r2) = mconcat [x1 `compare` x2,y1 `compare` y2,r1 `compare` r2]
    compare (IsReturnStmt s1 x1 y1) (IsReturnStmt s2 x2 y2) = mconcat [s1 `compare` s2,x1 `compare` x2,y1 `compare` y2]
    compare (DelayedCstr c1 _) (DelayedCstr c2 _) = c1 `compare` c2
    compare (MultipleSubstitutions v1 s1) (MultipleSubstitutions v2 s2) = mconcat [compare v1 v2,compare s1 s2]
    compare x y = constrIndex (toConstr x) `compare` constrIndex (toConstr y)

instance PP TCstr where
    pp (TRet t x) = text "tret" <+> pp t <+> char '=' <+> pp x
    pp (TDec n ts x) = text "tdec" <+> pp n <+> sepBy space (map pp ts) <+> char '=' <+> pp x
    pp (PDec n ts r x) = pp r <+> pp n <+> parens (sepBy comma (map pp ts)) <+> char '=' <+> pp x
    pp (Equals t1 t2) = text "equals" <+> pp t1 <+> pp t2
    pp (Coerces t1 t2) = text "coerces" <+> pp t1 <+> pp t2
    pp (CoercesSec t1 t2 b) = text "coercessec" <+> pp t1 <+> pp t2 <+> pp b
    pp (Coerces2Sec t1 t2 b x) = text "coerces2sec" <+> pp t1 <+> pp t2 <+> pp b <+> char '=' <+> pp x
    pp (Coerces2 t1 t2 x) = text "coerces2" <+> pp t1 <+> pp t2 <+> char '=' <+> pp x
    pp (Unifies t1 t2) = text "unifies" <+> pp t1 <+> pp t2
    pp (SupportedPrint ts) = text "print" <+> sepBy space (map pp ts)
    pp (ProjectStruct t a x) = pp t <> char '.' <> pp a <+> char '=' <+> pp x
    pp (ProjectMatrix t as x) = pp t <> brackets (sepBy comma $ map pp as) <+> char '=' <+> pp x
    pp (IsReturnStmt cs t dec) = text "return" <+> (hcat $ map pp $ Set.toList cs) <+> pp t <+> pp dec
    pp (DelayedCstr c f) = text "delayed" <+> pp c
    pp (MultipleSubstitutions v s) = text "multiplesubstitutions" <+> pp v <+> pp (map fst s)
    
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
    
instance MonadIO m => Vars m ArrayProj where
    traverseVars f (ArraySlice i1 i2) = do
        i1' <- f i1
        i2' <- f i2
        return $ ArraySlice i1' i2'
    traverseVars f (ArrayIdx w) = do
        w' <- f w
        return $ ArrayIdx w'
    
instance PP [Type] where
    pp xs = brackets $ sepBy comma $ map pp xs
    
instance MonadIO m => Vars m [Type] where
    traverseVars f xs = mapM f xs
    
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
    
instance MonadIO m => Vars m ArrayIndex where
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
    
instance MonadIO m => Vars m TCstr where
    traverseVars f (TRet t x) = do
        t' <- f t
        x' <- f x
        return $ TRet t' x'
    traverseVars f (TDec n args x) = do
        n' <- f n
        args' <- mapM f args
        x' <- f x
        return $ TDec n' args' x'
    traverseVars f (PDec n args ret x) = do
        n' <- f n
        x' <- f x
        args' <- mapM f args
        ret' <- f ret
        return $ PDec n' args' ret' x'
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
    traverseVars f (Coerces2 t1 t2 x) = do
        t1' <- f t1
        t2' <- f t2
        x' <- f x
        return $ Coerces2 t1' t2' x'
    traverseVars f (Coerces2Sec t1 t2 b x) = do
        t1' <- f t1
        t2' <- f t2
        b' <- f b
        x' <- f x
        return $ Coerces2Sec t1' t2' b' x'
    traverseVars f (Unifies t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ Unifies t1' t2'
    traverseVars f (SupportedPrint ts) = do
        ts' <- mapM f ts
        return $ SupportedPrint ts'
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
    traverseVars f (DelayedCstr c err) = do
        c' <- f c
        return $ DelayedCstr c' err
    traverseVars f (MultipleSubstitutions v s) = do
        v' <- f v
        s' <- mapM f s
        return $ MultipleSubstitutions v' s'

-- | Template constraint dictionary
-- a dictionary with a set of inferred constraints and resolved constraints
data TDict loc = TDict
    { tCstrs :: Map Unique (Loc loc IOCstr) -- a list of constraints
    , tChoices :: Set Unique -- set of choice constraints that have already been branched
    , tSubsts :: TSubsts -- variable substitions
    }
  deriving (Typeable,Eq,Data,Ord,Show)

-- | mappings from variables to current substitution
type TSubsts = Map (VarName VarIdentifier ()) Type

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
    | Evaluated -- has been evaluated
    | Erroneous -- has failed
        SecrecError -- failure error
  deriving (Data,Typeable,Show)

instance Functor TDict where
    fmap f dict = dict { tCstrs = Map.map (mapLoc f) (tCstrs dict) }

instance Monoid (TDict loc) where
    mempty = TDict Map.empty Set.empty Map.empty
    mappend (TDict u1 c1 ss1) (TDict u2 c2 ss2) = TDict (Map.union u1 u2) (Set.union c1 c2) (ss1 `Map.union` ss2)

addCstrDeps :: IOCstr -> IO ()
addCstrDeps iok = do
    let vs = tCstrVars (kCstr iok)
    g <- liftM tDeps $ readIORef globalEnv
    forM_ vs $ \v -> do
        mb <- WeakHash.lookup g (varNameId v)
        m <- maybe (WeakMap.new >>= \m -> WeakHash.insertWithMkWeak g (varNameId v) m (MkWeak $ mkWeakKey m) >> return m) return mb
        WeakMap.insertWithMkWeak m (uniqId $ kStatus iok) (kStatus iok) (MkWeak $ mkWeakKey $ kStatus iok)
--    modifyIORef' globalEnv $ \g -> g { tDeps = Map.unionWith Set.union (tDeps g) (Map.fromList $ zip vs $ repeat $ Set.singleton iok) }

tCstrVars :: TCstr -> [VarName VarIdentifier ()]
tCstrVars = everything (++) (mkQ [] aux1 `extQ` aux2 `extQ` aux3)
    where
    aux1 :: VarName VarIdentifier () -> [VarName VarIdentifier ()]
    aux1 v = [v]
    aux2 :: VarName VarIdentifier Type -> [VarName VarIdentifier ()]
    aux2 v = [fmap (const ()) v]
    aux3 :: VarName VarIdentifier (Typed Position) -> [VarName VarIdentifier ()]
    aux3 v = [fmap (const ()) v]

instance (Location loc,MonadIO m,Vars m loc) => Vars m (TDict loc) where
    traverseVars f (TDict cstrs choices substs) = varsBlock $ do
        let cstrsLst = Map.toList cstrs
        cstrs' <- mapM (f . snd) $ cstrsLst
        let cstrs'' = map (\x -> (uniqId $ kStatus $ unLoc x,x)) cstrs'
        let keys = zip (map fst cstrsLst) (map fst cstrs'')
        let choices' = Set.map (\x -> maybe x id $ lookup x keys) choices
        liftIO $ mapM_ (addCstrDeps . unLoc . snd) cstrs''
        substs' <- liftM Map.fromList $ mapM (\(x,y) -> do { x' <- f x; y' <- f y; return (x',y') }) $ Map.toList substs
        return $ TDict (Map.fromList cstrs'') choices' substs'

instance (Vars m loc,Vars m a) => Vars m (Loc loc a) where
    traverseVars f (Loc l a) = do
        l' <- f l
        a' <- f a
        return $ Loc l' a'

instance MonadIO m => Vars m IOCstr where
    traverseVars f (IOCstr k ref) = do
        k' <- f k
        ref' <- liftIO $ readUniqRef ref >>= newUniqRef
        return $ IOCstr k' ref'

substFromTDict :: (VarsTcM loc,Location loc,Vars (TcM loc) a) => loc -> TDict loc -> a -> TcM loc a
substFromTDict l dict = substFromTSubsts l (tSubsts dict)

substFromTSubsts :: (VarsTcM loc,Location loc,Vars (TcM loc) a) => loc -> TSubsts -> a -> TcM loc a
substFromTSubsts l tys =
    substFromMap vars >=> substFromMap doms >=> substFromMap doms1 >=> substFromMap doms2 >=> substFromMap types >=> substFromMap types1 >=> substFromMap types2 >=> substFromMap tys >=> substFromMap secs >=> substFromMap complexes >=> substFromMap bases >=> substFromMap exprs >=> substFromMap exprsLoc
  where
    -- VarName VarIdentifier () --> VarName VarIdentifier Type
    vars = Map.foldrWithKey (\k t m -> case typeToVarName t of { Just v -> Map.insert k v m; otherwise -> m }) Map.empty tys
    -- DomainName VarIdentifier () --> Domainname VarIdentifier Type
    doms = Map.foldrWithKey (\(VarName kl kn) t m -> case typeToVarName t of { Just (VarName vl vn) -> Map.insert (DomainName kl kn) (DomainName vl vn) m; otherwise -> m }) Map.empty tys
    -- DomainName VarIdentifier () --> DomainName VarIdentifier ()
    doms1 = Map.foldrWithKey (\(VarName kl kn) t m -> case typeToVarName t of { Just (VarName vl vn) -> Map.insert (DomainName kl kn) (DomainName () vn) m; otherwise -> m }) Map.empty tys
    -- DomainName VarIdentifier () --> DomainName VarIdentifier (Typed loc)
    doms2 = Map.foldrWithKey (\(VarName kl kn) t m -> case typeToVarName t of { Just (VarName vl vn) -> Map.insert (DomainName kl kn) (DomainName (Typed l vl) vn) m; otherwise -> m }) Map.empty tys
    -- TypeName VarIdentifier () --> TypeName VarIdentifier Type
    types = Map.foldrWithKey (\(VarName kl kn) t m -> case typeToVarName t of { Just (VarName vl vn) -> Map.insert (TypeName kl kn) (TypeName vl vn) m; otherwise -> m }) Map.empty tys
    -- TypeName VarIdentifier () --> TypeName VarIdentifier ()
    types1 = Map.foldrWithKey (\(VarName kl kn) t m -> case typeToVarName t of { Just (VarName vl vn) -> Map.insert (TypeName kl kn) (TypeName () vn) m; otherwise -> m }) Map.empty tys
    -- TypeName VarIdentifier () --> TypeName VarIdentifier (Typed loc)
    types2 = Map.foldrWithKey (\(VarName kl kn) t m -> case typeToVarName t of { Just (VarName vl vn) -> Map.insert (TypeName kl kn) (TypeName (Typed l vl) vn) m; otherwise -> m }) Map.empty tys
    -- VarName VarIdentifier () --> SecType
    secs = Map.foldrWithKey (\k t m -> case t of { SecT s -> Map.insert k s m; otherwise -> m }) Map.empty tys
    -- VarName VarIdentifier () --> ComplexType
    complexes = Map.foldrWithKey (\k t m -> case t of { ComplexT s -> Map.insert k s m; otherwise -> m }) Map.empty tys
    -- VarName VarIdentifier () --> BaseType
    bases = Map.foldrWithKey (\k t m -> case t of { BaseT s -> Map.insert k s m; otherwise -> m }) Map.empty tys
    -- VarName VarIdentifier () --> Expression VarIdentifier Type
    exprs = Map.foldrWithKey (\k t m -> case t of { IdxT s -> Map.insert k s m; otherwise -> m }) Map.empty tys
    -- VarName VarIdentifier () --> Expression VarIdentifier (Typed loc)
    exprsLoc = Map.foldrWithKey (\k t m -> case t of { IdxT s -> Map.insert k (fmap (Typed l) s) m; otherwise -> m }) Map.empty tys

--substFromSubstsType :: Vars a => SubstsType -> a -> a
--substFromSubstsType xs = substFromMap xs

--substFromSubstsVal :: (Vars loc,Location loc,Vars a) => SubstsVal loc -> a -> a
--substFromSubstsVal xs = substFromMap xs . substFromMap ys
--    where
--    ys = Map.map (fmap typed) xs

--tSolved :: TDict loc -> Map (Loc loc TCstr) Type
--tSolved = undefined -- TODO
--Map.foldrWithKey (\k v m -> maybe m (\x -> Map.insert k x m) v) Map.empty . tCstrs

--tUnsolved :: TDict loc -> [Loc loc TCstr]
--tUnsolved = undefined -- TODO
--Map.keys . Map.filter isNothing . tCstrs

insertTDictCstr :: loc -> TCstr -> TCstrStatus -> TDict loc -> TcM loc (IOCstr,TDict loc)
insertTDictCstr l c res dict = do
    st <- liftIO $ newUniqRef res
    let io = IOCstr c st
    return (io,dict { tCstrs = Map.insert (uniqId $ kStatus io) (Loc l io) (tCstrs dict) })

instance PP (TDict loc) where
    pp dict = text "Constraints:" $+$ nest 4 (vcat $ map pp $ Map.elems $ tCstrs dict)
          $+$ text "Substitutions:" $+$ nest 4 (ppTSubsts (tSubsts dict))

ppConstraints :: TDict loc -> TcM loc Doc
ppConstraints d = do
    let ppK (Loc l c) = do
        s <- liftIO $ readUniqRef $ kStatus c
        let pre = pp (kCstr c) <+> text (show $ hashUnique $ uniqId $ kStatus c)
        case s of
            Evaluated -> return $ pre <> char '=' <+> text "OK"
            Unevaluated -> return $ pre
            Erroneous err -> return $ pre <> char '=' <+> if isHaltError err then text "HALT" else text "ERROR"
    ss <- liftM vcat $ mapM ppK (Map.elems $ tCstrs d)
    return ss

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
        PIdentifier
        [VarName VarIdentifier Type] -- typed procedure arguments
        Type -- return type
        [Statement VarIdentifier (Typed Position)] -- ^ the procedure's body
    | StructType -- ^ Struct type
            TyVarId -- ^ unique structure declaration id
            Position -- ^ location of the procedure declaration
            SIdentifier
            [Attribute VarIdentifier Type] -- ^ typed arguments
    | TpltType -- ^ Template type
            TyVarId -- ^ unique template declaration id
            [VarName VarIdentifier Type] -- ^ template variables
            (TDict Position) -- ^ template constraints depending on the variables
            [Type] -- ^ template specializations
            DecType -- ^ template's type
    | DVar -- declaration variable
        (VarName VarIdentifier ())
  deriving (Typeable,Show,Data)

instance Eq DecType where
    (DVar v1) == (DVar v2) = v1 == v2
    x == y = decTypeTyVarId x == decTypeTyVarId y
instance Ord DecType where
    compare (DVar v1) (DVar v2) = compare v1 v2
    compare x y = compare (decTypeTyVarId x) (decTypeTyVarId y)

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
    | ArrayLit -- ^ a concrete array
        (NeList (Expression VarIdentifier Type))
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
    | IdxT (Expression VarIdentifier Type) -- for index expressions
  deriving (Typeable,Show,Data,Eq,Ord)

instance PP SecType where
    pp Public = text "public"
    pp (Private d k) = pp d
    pp (SVar (VarName _ v) k) = parens (ppVarId v <+> text "::" <+> pp k)
instance PP DecType where
    pp = ppTpltDecType
instance PP BaseType where
    pp (TyPrim p) = pp p
    pp (TyDec d) = pp d
    pp (BVar (VarName _ v)) = ppVarId v
instance PP ComplexType where
    pp (TyLit lit) = pp lit
    pp (ArrayLit es) = braces (sepBy comma $ map pp $ Foldable.toList es)
    pp Void = text "void"
    pp (CType s t d szs) = pp s <+> pp t <> brackets (brackets (pp d)) <> parens (sepBy comma $ map pp szs)
    pp (CVar (VarName _ v)) = ppVarId v
instance PP SysType where
    pp t@(SysPush {}) = text (show t)
    pp t@(SysRet {}) = text (show t)
    pp t@(SysRef {}) = text (show t)
    pp t@(SysCRef {}) = text (show t)

instance PP Type where
    pp t@(NoType msg) = text (show t)
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

typeClass :: String -> Type -> TypeClass
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

isIntPrimType :: PrimitiveDatatype () -> Bool
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

isFloatPrimType :: PrimitiveDatatype () -> Bool
isFloatPrimType (DatatypeFloat32   _) = True
isFloatPrimType (DatatypeFloat64   _) = True
isFloatPrimType t = False

isNumericType :: Type -> Bool
isNumericType t = isIntType t || isFloatType t

isNumericBaseType :: BaseType -> Bool
isNumericBaseType t = isIntBaseType t || isFloatBaseType t

instance PP StmtClass where
    pp = text . show

instance Monad m => Vars m StmtClass where
    traverseVars f c = return c
  
instance Monad m => Vars m SecType where
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
            EqT -> return $ Just n
            NeqT -> return $ Nothing
    substL pl e = return $ Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
            EqT -> return $ Just r
            NeqT -> return $ Nothing

instance MonadIO m => Vars m [TCstr] where
    traverseVars f xs = mapM f xs

instance PP [TCstr] where
    pp xs = brackets (sepBy comma $ map pp xs)

instance MonadIO m => Vars m DecType where
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
    traverseVars f (TpltType tid vs d spes t) = varsBlock $ do
        vs' <- inLHS $ mapM f vs
        d' <- f d
        spes' <- mapM f spes
        t' <- f t
        return $ TpltType tid vs' d' spes' t'
    traverseVars f (DVar v) = do
        v' <- f v
        return $ DVar v'
    
instance MonadIO m => Vars m BaseType where
    traverseVars f (TyPrim p) = do
        p' <- f p
        return $ TyPrim p'
    traverseVars f (TyDec d) = do
        d' <- f d
        return $ TyDec d'
    traverseVars f (BVar v) = do
        v' <- f v
        return $ BVar v'
    substL pl (BVar v) =
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf v) of
            EqT -> return $ Just v
            NeqT -> return Nothing
    substL pl e = return Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
            EqT -> return $ Just r
            NeqT -> return Nothing

instance MonadIO m => Vars m ComplexType where
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
    substL pl (CVar v) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing
    substL pl e = return Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
            EqT -> return $ Just r
            NeqT -> return Nothing

instance MonadIO m => Vars m SysType where
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

instance Monad m => Vars m SVarKind where
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
    
instance MonadIO m => Vars m Type where
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
    substL pl (BaseT (BVar v)) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return $ Nothing
    substL pl (SecT (SVar v _)) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return $ Nothing
    substL pl (ComplexT (CVar v)) = let n = v in
        case eqTypeOf (typeOfProxy pl) (typeOfProxy $ proxyOf n) of
            EqT -> return $ Just n
            NeqT -> return Nothing
    substL pl e = return Nothing
    substR pa r =
        case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy (Proxy::Proxy (VarName VarIdentifier Type))) of
            EqT -> return $ Just $ varNameToType r
            NeqT -> case eqTypeOf (typeOfProxy $ proxyOf r) (typeOfProxy pa) of
                EqT -> return $ Just r
                NeqT -> return Nothing

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

instance (MonadIO m,Vars m a) => Vars m (Typed a) where
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
decTypeTyVarId (TpltType i _ _ _ _) = Just i
decTypeTyVarId (DVar _) = Nothing

instance Location Type where
    locpos = const noloc
    noloc = NoType "noloc"
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

ppTpltType :: Type -> Doc
ppTpltType (DecT t) = ppTpltDecType t

ppTpltDecType :: DecType -> Doc
ppTpltDecType (TpltType _ vars _ specs body@(StructType _ _ n _)) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ text "struct" <+> pp n <> abrackets (sepBy comma $ map pp specs) <+> braces (text "...")
ppTpltDecType (TpltType _ vars _ [] body@(ProcType _ _ (Left n) args ret stmts)) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ pp ret <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (text "...")
ppTpltDecType (TpltType _ vars _ [] body@(ProcType _ _ (Right n) args ret stmts)) =
        text "template" <> abrackets (sepBy comma $ map ppTpltArg vars)
    $+$ pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (text "...")
ppTpltDecType (ProcType _ _ (Left n) args ret stmts) =
        pp ret <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (text "...")
ppTpltDecType (ProcType _ _ (Right n) args ret stmts) =
        pp ret <+> text "operator" <+> pp n <> parens (sepBy comma $ map (\(VarName t n) -> pp t <+> pp n) args) <+> braces (text "...")
ppTpltDecType (DVar v) = pp v

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
    
ppTSubsts :: TSubsts -> Doc
ppTSubsts xs = vcat $ map ppSub $ Map.toList xs
    where
    ppSub (VarName _ k,t) = ppVarId k <+> char '=' <+> pp t
    
--ppSubstsGeneric :: SubstsGeneric loc -> Doc
--ppSubstsGeneric xs = vcat $ map ppSub $ Map.toList xs
--    where
--    ppSub (VarName _ k,Left t) = ppVarId k <+> char '=' <+> pp t
--    ppSub (VarName _ k,Right e) = ppVarId k <+> char '=' <+> pp e
--
--ppSubstsType :: SubstsType -> Doc
--ppSubstsType xs = vcat $ map ppSub $ Map.toList xs
--    where
--    ppSub (VarName _ k,t) = ppVarId k <+> char '=' <+> pp t
--
--ppSubstsVal :: SubstsVal loc -> Doc
--ppSubstsVal xs = vcat $ map ppSub $ Map.toList xs
--    where
--    ppSub (VarName _ k,e) = ppVarId k <+> char '=' <+> pp e

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

instance Monad m => Vars m HsVal where
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
primIntBounds :: PrimitiveDatatype () -> Maybe (Integer,Integer)
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

primFloatBounds :: PrimitiveDatatype () -> Maybe (Double,Double)
primFloatBounds (DatatypeFloat32 _) = Just (-2.802597 * 10 ^^(-45),3.402823 * (10 ^^38))
primFloatBounds (DatatypeFloat64 _) = Just (-4.940656 * 10 ^^ (-324),1.797693 * (10 ^^308))
primFloatBounds _ = Nothing

bytes :: ComplexType
bytes = CType Public (TyPrim $ DatatypeUint8 ()) (indexExpr 1) []
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
defCType t = CType Public t (indexExpr 0) []

instance Hashable VarIdentifier where
    hashWithSalt i v = hashWithSalt (maybe i (i+) $ varIdUniq v) (varIdBase v)