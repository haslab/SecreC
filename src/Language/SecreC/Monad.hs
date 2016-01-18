{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, TupleSections, MultiParamTypeClasses #-}

module Language.SecreC.Monad where
    
import Language.SecreC.Error
import Language.SecreC.Location
import Language.SecreC.Pretty
    
import Control.Monad.IO.Class
import Control.Monad.Except
import Control.Monad.Writer
import Control.Applicative
import Control.Monad.Catch
import Control.Exception (throwIO)
import Control.Monad.Signatures
import Control.Monad.Reader (MonadReader,ReaderT(..),ask,local)
import qualified Control.Monad.Reader as Reader

import Data.Generics
import Data.Map as Map

import Text.PrettyPrint

import System.IO

-- | SecreC options
data Options
    = Opts  { 
          inputs                :: [FilePath]
        , outputs               :: [FilePath]
        , paths                 :: [FilePath]
        , parser                :: ParserOpt
        , knowledgeInference    :: Bool
        , typeCheck             :: Bool
        , debugLexer            :: Bool
        , debugParser           :: Bool
        , debugTypechecker      :: Bool
        , constraintStackSize   :: Int
        , evalTimeOut           :: Int
        , implicitClassify      :: Bool
        , implicitBuiltin       :: Bool
        , externalSMT           :: Bool
        }
    deriving (Show, Data, Typeable)

data ParserOpt = Parsec | Derp
  deriving (Data,Typeable,Read,Show)

defaultOptions :: Options
defaultOptions = Opts
    { inputs = []
    , outputs = []
    , paths = []
    , parser = Parsec
    , knowledgeInference = False
    , typeCheck = True
    , debugLexer = False
    , debugParser = False
    , debugTypechecker = False
    , constraintStackSize = 10
    , evalTimeOut = 5
    , implicitClassify = True
    , implicitBuiltin = True
    , externalSMT = True
    }

type SecrecWarnings = Map Int SecrecWarning

-- | SecreC Monad
data SecrecM m a = SecrecM { unSecrecM :: ReaderT Options m (Either SecrecError (a,SecrecWarnings)) }
  deriving (Typeable)

mapSecrecM :: (m (Either SecrecError (a,SecrecWarnings)) -> n (Either SecrecError (b,SecrecWarnings))) -> SecrecM m a -> SecrecM n b
mapSecrecM f (SecrecM m) = SecrecM $ Reader.mapReaderT f m

runSecrecMWith :: Options -> SecrecM m a -> m (Either SecrecError (a,SecrecWarnings))
runSecrecMWith opts m = flip runReaderT opts $ unSecrecM m

runSecrecM :: MonadIO m => Options -> SecrecM m a -> m a
runSecrecM opts m = flip runReaderT opts $ do
    e <- unSecrecM m
    case e of
        Left err -> liftIO $ throwError $ userError $ ppr err
        Right (x,warns) -> do
            forM_ warns $ \w -> liftIO $ hPutStrLn stderr (ppr w)
            return x

instance Monad m => MonadReader Options (SecrecM m) where
    ask = SecrecM $ liftM (Right . (,Map.empty)) ask
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
    liftIO io = SecrecM $ liftIO $ liftM (Right . (,Map.empty)) io

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
    return x = SecrecM $ return $ Right (x,Map.empty)
    (SecrecM m) >>= f = SecrecM $ do
        ex <- m
        case ex of
            Left err -> return (Left err)
            Right (x,wsx) -> do
                ey <- unSecrecM (f x)
                case ey of
                    Left err -> return (Left err)
                    Right (y,wsy) -> return (Right (y,wsx `Map.union` wsy))

instance Monad m => Applicative (SecrecM m) where
    pure = return
    (<*>) = ap

mapError :: MonadError SecrecError m => (SecrecError -> SecrecError) -> m a -> m a
mapError f m = m `catchError` (throwError . f)


