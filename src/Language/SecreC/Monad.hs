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
        , constraintStackSize   :: Int
        }
    | Help
    deriving (Show, Data, Typeable)

data ParserOpt = Parsec | Derp
  deriving (Data,Typeable,Read,Show)

defaultOptions :: Options
defaultOptions = Opts [] [] [] Parsec False True False False 5

-- | SecreC Monad
data SecrecM a = SecrecM { runSecrecM :: ReaderT Options IO (Either SecrecError (a,[SecrecWarning])) }
  deriving (Typeable)

ioSecrecM :: Options -> SecrecM a -> IO a
ioSecrecM opts m = flip runReaderT opts $ do
    e <- runSecrecM m
    case e of
        Left err -> throwError $ userError $ ppr err
        Right (x,warns) -> do
            forM_ warns $ \w -> lift $ hPutStrLn stderr (ppr w)
            return x

instance MonadReader Options SecrecM where
    ask = SecrecM $ liftM (Right . (,[])) ask
    local f (SecrecM m) = SecrecM $ local f m 

instance MonadWriter [SecrecWarning] SecrecM where
    writer (x,ws) = SecrecM $ return $ Right (x,ws)
    listen (SecrecM io) = SecrecM $ liftM (either Left (\(x,ws) -> Right ((x,ws),ws))) io
    pass (SecrecM io) = SecrecM $ liftM (either Left (\((x,f),ws) -> Right (x,f ws))) io

instance MonadError SecrecError SecrecM where
    throwError e = SecrecM $ return $ Left e
    catchError (SecrecM m) f = SecrecM $ do
        x <- m
        case x of
            Left err -> runSecrecM (f err)
            otherwise -> return x

instance MonadIO SecrecM where
    liftIO io = SecrecM $ lift $ liftM (Right . (,[])) io

instance MonadThrow SecrecM where
    throwM e = liftIO $ throwIO e

instance MonadCatch SecrecM where
    catch = liftCatch catch

instance MonadPlus SecrecM where
    mzero = genericError noloc (text "mzero")
    mplus x y = catchError x (const y)
    
instance Alternative SecrecM where
    empty = mzero
    (<|>) = mplus

liftCatch :: Catch e (ReaderT Options IO) (Either SecrecError (a,[SecrecWarning])) -> Catch e SecrecM a
liftCatch catchE m h = SecrecM $ runSecrecM m `catchE` \ e -> runSecrecM (h e)

instance MonadMask SecrecM where
    mask a = SecrecM $ mask $ \u -> runSecrecM (a $ liftMask u)
    uninterruptibleMask a = SecrecM $ uninterruptibleMask $ \u -> runSecrecM (a $ liftMask u)

liftMask :: (ReaderT Options IO ((Either SecrecError (a,[SecrecWarning]))) -> ReaderT Options IO ((Either SecrecError (a,[SecrecWarning])))) -> SecrecM a -> SecrecM a
liftMask u (SecrecM b) = SecrecM (u b)

instance Functor SecrecM where
    fmap f (SecrecM m) = SecrecM $ do
        e <- m
        case e of
            Left err -> return (Left err)
            Right (x,w) -> return (Right (f x,w))
            
instance Monad SecrecM where
    return x = SecrecM $ return $ Right (x,[])
    (SecrecM m) >>= f = SecrecM $ do
        ex <- m
        case ex of
            Left err -> return (Left err)
            Right (x,wsx) -> do
                ey <- runSecrecM (f x)
                case ey of
                    Left err -> return (Left err)
                    Right (y,wsy) -> return (Right (y,wsx ++ wsy))

instance Applicative SecrecM where
    pure = return
    (<*>) = ap

mapError :: MonadError SecrecError m => (SecrecError -> SecrecError) -> m a -> m a
mapError f m = m `catchError` (throwError . f)

