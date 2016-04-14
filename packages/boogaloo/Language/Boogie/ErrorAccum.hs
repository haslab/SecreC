{-# LANGUAGE TupleSections, StandaloneDeriving #-}

-- | This monad transformer adds the ability to accumulate errors from several ExceptT computations
-- and report them all at once.
module Language.Boogie.ErrorAccum where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Except

-- | Error accumulator: 
-- used in combination with ExceptT to store intermediate computation results, 
-- when errors should be accumulated rather than reported immediately  
newtype ErrorAccumT e m a = ErrorAccumT { runErrorAccumT :: m ([e], a) }

instance MonadTrans (ErrorAccumT e) where
    lift m = ErrorAccumT $ liftM ([],) m

instance (Monad m) => Functor (ErrorAccumT e m) where
    fmap = liftM

instance (Monad m) => Applicative (ErrorAccumT e m) where
  -- | Attach an empty list of errors to a succesful computation
  pure x  = ErrorAccumT $ return ([], x)
  -- | The bind strategy is to concatenate error lists
  (<*>) = ap

instance (Monad m) => Monad (ErrorAccumT e m) where
  -- | Attach an empty list of errors to a succesful computation
  return = pure
  -- | The bind strategy is to concatenate error lists
  m >>= k   = ErrorAccumT $ do
    (errs, res) <- runErrorAccumT m
    (errs', res') <- runErrorAccumT $ k res
    return (errs ++ errs', res')

    
--instance ErrorList e => MonadTrans (ErrorAccumT e) where
--  lift m = ErrorAccumT $ do
--    a <- m
--    return ([], a)  
    
-- | Transform an error computation and default value into an error accumlator
accum :: (Monad m) => ExceptT [e] m a -> a -> ErrorAccumT e m a
accum c def = ErrorAccumT (errToAccum def `liftM` runExceptT c)
  where
    errToAccum def (Left errs)  = (errs, def)
    errToAccum def (Right x)    = ([], x)
        
-- | Transform an error accumlator back into a regular error computation  
report :: (Monad m) => ErrorAccumT e m a -> ExceptT [e] m a
report accum = ExceptT (accumToErr `liftM` runErrorAccumT accum)
  where
    accumToErr ([], x) = Right x
    accumToErr (es, _) = Left es  

-- | 'mapAccum' @f def xs@ :
-- Apply @f@ to all @xs@, accumulating errors and reporting them at the end
mapAccum :: (Monad m) => (a -> ExceptT [e] m b) -> b -> [a] -> ExceptT [e] m [b]
mapAccum f def xs = report $ mapM (acc f) xs  
  where
    acc f x  = accum (f x) def
   
-- | 'mapAccumA_' @f xs@ :
-- Apply @f@ to all @xs@ throwing away the result, accumulating errors
mapAccumA_ :: (Monad m) => (a -> ExceptT [e] m ()) -> [a] -> ErrorAccumT e m ()
mapAccumA_ f xs = mapM_ (acc f) xs  
  where
    acc f x  = accum (f x) ()
    
-- | Same as 'mapAccumA_', but reporting errors at the end
mapAccum_ :: (Monad m) => (a -> ExceptT [e] m ()) -> [a] -> ExceptT [e] m ()
mapAccum_ f xs = report $ mapAccumA_ f xs  

-- | 'zipWithAccum_' @f xs ys@ :
-- Apply type checking @f@ to all @xs@ and @ys@ throwing away the result,
-- accumulating errors and reporting them at the end
zipWithAccum_ :: (Monad m) => (a -> b -> ExceptT [e] m ()) -> [a] -> [b] -> ExceptT [e] m ()
zipWithAccum_ f xs ys = report $ zipWithM_ (acc f) xs ys  
  where
    acc f x y  = accum (f x y) ()
