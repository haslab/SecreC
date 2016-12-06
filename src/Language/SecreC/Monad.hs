{-# LANGUAGE DeriveGeneric, TypeFamilies, FlexibleContexts, FlexibleInstances, DeriveDataTypeable, TupleSections, MultiParamTypeClasses #-}

module Language.SecreC.Monad where
    
import Language.SecreC.Error
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.Position
    
import Control.Monad
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Except (MonadError(..))
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Applicative
import Control.Monad.Catch
import Control.Exception (throwIO)
import Control.Monad.Signatures
import Control.Monad.Reader (MonadReader,ask,local)
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer
import Control.Monad.Trans.Control
import Control.Monad.Base

import Data.Generics hiding (Generic)
import Data.Binary
import Data.Hashable
import Data.Map as Map
import Data.Set as Set
import Data.List as List

import Text.PrettyPrint
import qualified Text.ParserCombinators.ReadPrec as Read

import System.IO
import System.Exit

import GHC.Generics (Generic)

data PromoteOpt = NoP | LocalP | GlobalP
    deriving (Data, Typeable,Generic,Eq,Show,Read)
instance Binary PromoteOpt
instance Hashable PromoteOpt

instance Monad m => PP m PromoteOpt where
    pp NoP = return $ text "nop"
    pp LocalP = return $ text "localp"
    pp GlobalP = return $ text "globalp"

appendPromoteOpt :: PromoteOpt -> PromoteOpt -> PromoteOpt
appendPromoteOpt x y | x == y = x
appendPromoteOpt LocalP y = y
appendPromoteOpt x LocalP = x
appendPromoteOpt NoP y = NoP
appendPromoteOpt x NoP = NoP
appendPromoteOpt GlobalP y = y
appendPromoteOpt x GlobalP = x

data VerifyOpt = NoneV | FuncV | LeakV | BothV
    deriving (Data, Typeable,Generic,Eq,Show,Read)
instance Binary VerifyOpt
instance Hashable VerifyOpt

instance Monad m => PP m VerifyOpt where
    pp NoneV = return $ text "nonev"
    pp FuncV = return $ text "funcv"
    pp LeakV = return $ text "leakv"
    pp BothV = return $ text "bothv"

appendVerifyOpt :: VerifyOpt -> VerifyOpt -> VerifyOpt
appendVerifyOpt x y | x == y = x
appendVerifyOpt NoneV y = y
appendVerifyOpt x NoneV = x
appendVerifyOpt FuncV LeakV = BothV
appendVerifyOpt FuncV BothV = BothV
appendVerifyOpt LeakV FuncV = BothV
appendVerifyOpt LeakV BothV = BothV
appendVerifyOpt BothV _ = BothV

data ContextOpt = DelayCtx | InferCtx
    deriving (Data, Typeable,Generic,Eq,Ord,Show,Read)
instance Binary ContextOpt
instance Hashable ContextOpt

instance Monad m => PP m ContextOpt where
    pp DelayCtx = return $ text "delayctx"
    pp InferCtx = return $ text "inferctx"

data BacktrackOpt = NoneB | TryB | FullB
    deriving (Data, Typeable,Generic,Eq,Ord,Show,Read)
instance Binary BacktrackOpt
instance Hashable BacktrackOpt

instance Monad m => PP m BacktrackOpt where
    pp NoneB = return $ text "noneb"
    pp TryB = return $ text "tryb"
    pp FullB = return $ text "fullb"

data MatchingOpt = OrderedM | GOrderedM | UnorderedM
    deriving (Data, Typeable,Generic,Eq,Ord,Show,Read)
instance Binary MatchingOpt
instance Hashable MatchingOpt

instance Monad m => PP m MatchingOpt where
    pp OrderedM = return $ text "orderedm"
    pp GOrderedM = return $ text "gorderedm"
    pp UnorderedM = return $ text "unorderedm"


data CoercionOpt = OffC | DefaultsC | OnC | ExtendedC
    deriving (Data, Typeable,Generic,Eq,Ord,Show,Read)
instance Binary CoercionOpt
instance Hashable CoercionOpt

instance Monad m => PP m CoercionOpt where
    pp OffC = return $ text "offc"
    pp DefaultsC = return $ text "defaultsc"
    pp OnC = return $ text "onc"
    pp ExtendedC = return $ text "extendedc"

appendContextOpt :: ContextOpt -> ContextOpt -> ContextOpt
appendContextOpt x y = max x y

appendCoercionOpt :: CoercionOpt -> CoercionOpt -> CoercionOpt
appendCoercionOpt ExtendedC _ = ExtendedC
appendCoercionOpt _ ExtendedC = ExtendedC
appendCoercionOpt x y = min x y

preprocessArgs :: [String] -> [String]
preprocessArgs xs = List.map preprocessArg xs
    where
    preprocessArg "--verify" = "--verify=bothv"
    preprocessArg x = x

-- | SecreC options
data Options
    = Opts  { 
          inputs                :: [FilePath]
        , outputs               :: [FilePath]
        , paths                 :: [FilePath]
        , verify                :: VerifyOpt
        , simplify              :: Bool
        , typeCheck             :: Bool
        , debugLexer            :: Bool
        , debugParser           :: Bool
        , debugTypechecker      :: Bool
        , debugTransformation   :: Bool
        , debugVerification           :: Bool
        , constraintStackSize   :: Int
        , evalTimeOut           :: Int
        , implicitCoercions      :: CoercionOpt
        , promote           :: PromoteOpt
        , implicitContext        :: ContextOpt
        , backtrack              :: BacktrackOpt
        , matching               :: MatchingOpt
        , printOutput           :: Bool
        , debug :: Bool
        , writeSCI              :: Bool
        , failTypechecker       :: Bool
        , implicitBuiltin       :: Bool
        , externalSMT           :: Bool
        , checkAssertions       :: Bool
        , forceRecomp           :: Bool
        , entryPoints           :: [String]
        , defaults              :: Bool
        , progress              :: Bool
        }
    deriving (Show, Data, Typeable,Generic)
instance Binary Options
instance Hashable Options

instance Monoid Options where
    mempty = defaultOptions
    mappend x y = Opts
        { inputs = inputs x ++ inputs y
        , outputs = outputs x ++ outputs y
        , paths = List.nub $ paths x ++ paths y
        , verify = verify x `appendVerifyOpt` verify y
        , simplify = simplify x && simplify y
        , typeCheck = typeCheck x || typeCheck y
        , debugLexer = debugLexer x || debugLexer y
        , debugParser = debugParser x || debugParser y
        , debugTypechecker = debugTypechecker x || debugTypechecker y
        , debugTransformation = debugTransformation x || debugTransformation y
        , debugVerification = debugVerification x || debugVerification y
        , constraintStackSize = max (constraintStackSize x) (constraintStackSize y)
        , evalTimeOut = max (evalTimeOut x) (evalTimeOut y)
        , implicitCoercions = implicitCoercions x `appendCoercionOpt` implicitCoercions y
        , promote = promote x `appendPromoteOpt` promote y
        , implicitContext = implicitContext x `appendContextOpt` implicitContext y
        , backtrack = backtrack x `min` backtrack y
        , matching = matching x `min` matching y
        , printOutput = printOutput x || printOutput y
        , debug = debug x || debug y
        , writeSCI = writeSCI x && writeSCI y
        , implicitBuiltin = implicitBuiltin x && implicitBuiltin y
        , failTypechecker = failTypechecker x || failTypechecker y
        , externalSMT = externalSMT x && externalSMT y
        , checkAssertions = checkAssertions x || checkAssertions y
        , forceRecomp = forceRecomp x || forceRecomp y
        , entryPoints = entryPoints x ++ entryPoints y
        , defaults = defaults x && defaults y
        , progress = progress x || progress y
        }

defaultOptions :: Options
defaultOptions = Opts
    { inputs = []
    , entryPoints = []
    , outputs = []
    , paths = []
    , verify = NoneV
    , simplify = True
    , typeCheck = True
    , debugLexer = False
    , debugParser = False
    , debugTypechecker = False
    , debugTransformation = False
    , debugVerification = False
    , constraintStackSize = 100
    , evalTimeOut = 5
    , progress = False
    , implicitCoercions = OnC
    , promote = LocalP
    , implicitContext = DelayCtx
    , backtrack = FullB
    , matching = UnorderedM
    , printOutput = False
    , debug = False
    , writeSCI = True
    , implicitBuiltin = True
    , failTypechecker = False
    , externalSMT = True
    , checkAssertions = False
    , forceRecomp = False
    , defaults = True
    }

newtype SecrecWarnings = ScWarns { unScWarns :: Map Int (Map Position (Set SecrecWarning)) }
  deriving (Typeable)

instance Monoid SecrecWarnings where
    mempty = ScWarns Map.empty
    mappend (ScWarns x) (ScWarns y) = ScWarns $ Map.unionWith (Map.unionWith Set.union) x y

-- | SecreC Monad
data SecrecM m a = SecrecM { unSecrecM :: ReaderT Options m (Either SecrecError (a,SecrecWarnings)) }
  deriving (Typeable)

instance MonadTrans SecrecM where
    lift m = SecrecM $ lift $ liftM (Right . (,mempty)) m

instance MonadIO m => MonadBase IO (SecrecM m) where
    liftBase = liftIO

instance MonadIO m => MonadBaseControl IO (SecrecM m) where
    type StM (SecrecM m) a = SecrecM m a
    liftBaseWith f = liftIO $ f return
    restoreM       = id

mapSecrecM :: (m (Either SecrecError (a,SecrecWarnings)) -> n (Either SecrecError (b,SecrecWarnings))) -> SecrecM m a -> SecrecM n b
mapSecrecM f (SecrecM m) = SecrecM $ Reader.mapReaderT f m

runSecrecMWith :: Options -> SecrecM m a -> m (Either SecrecError (a,SecrecWarnings))
runSecrecMWith opts m = flip runReaderT opts $ unSecrecM m

printWarns :: SecrecWarnings -> IO ()
printWarns (ScWarns warns) = do
    forM_ warns $ \ws ->
        forM_ (Map.elems ws) $ \w ->
            forM_ w $ \x -> liftIO $ hPutStrLn stderr (pprid x)
            
flushWarnings :: MonadIO m => SecrecM m a -> SecrecM m a
flushWarnings (SecrecM m) = SecrecM $ do
    opts <- Reader.ask
    e <- lift $ runReaderT m opts
    case e of
        Left err -> return $ Left err
        Right (x,ws) -> do
            liftIO $ printWarns ws
            return $ Right (x,mempty)

runSecrecM :: MonadIO m => Options -> SecrecM m a -> m a
runSecrecM opts m = flip runReaderT opts $ do
    e <- unSecrecM m
    case e of
        Left err -> do
            ppe <- ppr err
            liftIO $ die $ ppe
        Right (x,warns) -> do
            liftIO $ printWarns warns
            return x

instance Monad m => MonadReader Options (SecrecM m) where
    ask = SecrecM $ liftM (Right . (,mempty)) ask
    local f (SecrecM m) = SecrecM $ local f m 

instance Monad m => MonadWriter SecrecWarnings (SecrecM m) where
    writer (x,ws) = SecrecM $ return $ Right (x,ws)
    listen (SecrecM io) = SecrecM $ liftM (either Left (\(x,ws) -> Right ((x,ws),ws))) io
    pass (SecrecM io) = SecrecM $ liftM (either Left (\((x,f),ws) -> Right (x,f ws))) io

instance Monad m => MonadError SecrecError (SecrecM m) where
    throwError e = SecrecM $ return $ Left e
    catchError (SecrecM m) f = SecrecM $ do
        x <- m
        case x of
            Left err -> unSecrecM (f err)
            otherwise -> return x

instance MonadIO m => MonadIO (SecrecM m) where
    liftIO io = SecrecM $ liftIO $ liftM (Right . (,mempty)) io

instance MonadThrow m => MonadThrow (SecrecM m) where
    throwM e = SecrecM $ lift $ throwM e

instance MonadCatch m => MonadCatch (SecrecM m) where
    catch = liftCatch catch

instance Monad m => MonadPlus (SecrecM m) where
    mzero = genError noloc (text "mzero")
    mplus x y = catchError x (const y)
    
instance Monad m => Alternative (SecrecM m) where
    empty = mzero
    (<|>) = mplus

liftCatch :: Catch e (ReaderT Options m) (Either SecrecError (a,SecrecWarnings)) -> Catch e (SecrecM m) a
liftCatch catchE m h = SecrecM $ unSecrecM m `catchE` \ e -> unSecrecM (h e)

instance MonadMask m => MonadMask (SecrecM m) where
    mask a = SecrecM $ mask $ \u -> unSecrecM (a $ liftMask u)
    uninterruptibleMask a = SecrecM $ uninterruptibleMask $ \u -> unSecrecM (a $ liftMask u)

liftMask :: (ReaderT Options m ((Either SecrecError (a,SecrecWarnings))) -> ReaderT Options m ((Either SecrecError (a,SecrecWarnings)))) -> SecrecM m a -> SecrecM m a
liftMask u (SecrecM b) = SecrecM (u b)

instance Monad m => Functor (SecrecM m) where
    fmap f (SecrecM m) = SecrecM $ do
        e <- m
        case e of
            Left err -> return (Left err)
            Right (x,w) -> return (Right (f x,w))
            
instance Monad m => Monad (SecrecM m) where
    return x = SecrecM $ return $ Right (x,mempty)
    (SecrecM m) >>= f = SecrecM $ do
        ex <- m
        case ex of
            Left err -> return (Left err)
            Right (x,wsx) -> do
                ey <- unSecrecM (f x)
                case ey of
                    Left err -> return (Left err)
                    Right (y,wsy) -> return (Right (y,wsx `mappend` wsy))

instance Monad m => Applicative (SecrecM m) where
    pure = return
    (<*>) = ap

mapError :: MonadError SecrecError m => (SecrecError -> SecrecError) -> m a -> m a
mapError f m = m `catchError` (throwError . f)

warn :: (MonadWriter SecrecWarnings m,MonadError SecrecError m) => Position -> SecrecError -> m ()
warn pos e = Writer.tell $ ScWarns $ Map.singleton 0 $ Map.singleton pos $ Set.singleton $ ErrWarn e
