{-# LANGUAGE FlexibleInstances, DeriveDataTypeable, TupleSections, MultiParamTypeClasses #-}

module Language.SecreC.Monad where
    
import Language.SecreC.Error
    
import Control.Monad.IO.Class
import Control.Monad.Except
import Control.Monad.Writer
import Control.Applicative
import Control.Monad.Catch
import Control.Exception (throwIO)
import Control.Monad.Signatures
import Data.Generics

import System.IO

data SecrecM a = SecrecM { runSecrecM :: IO (Either SecrecError (a,[SecrecWarning])) }
  deriving (Data,Typeable)

ioSecrecM :: SecrecM a -> IO a
ioSecrecM m = do
    e <- runSecrecM m
    case e of
        Left err -> throwError $ userError $ show err
        Right (x,warns) -> do
            forM_ warns $ \w -> hPutStrLn stderr (show w)
            return x

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
    liftIO io = SecrecM $ liftM (Right . (,[])) io

instance MonadThrow SecrecM where
	throwM e = liftIO $ throwIO e

instance MonadCatch SecrecM where
    catch = liftCatch catch

liftCatch :: Catch e IO (Either SecrecError (a,[SecrecWarning])) -> Catch e SecrecM a
liftCatch catchE m h = SecrecM $ runSecrecM m `catchE` \ e -> runSecrecM (h e)

instance MonadMask SecrecM where
	mask a = SecrecM $ mask $ \u -> runSecrecM (a $ liftMask u)	
	uninterruptibleMask a = SecrecM $ uninterruptibleMask $ \u -> runSecrecM (a $ liftMask u)

liftMask :: (IO ((Either SecrecError (a,[SecrecWarning]))) -> IO ((Either SecrecError (a,[SecrecWarning])))) -> SecrecM a -> SecrecM a
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
    