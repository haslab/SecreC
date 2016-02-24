{-# LANGUAGE DeriveDataTypeable, GADTs, ScopedTypeVariables, TypeFamilies, MultiParamTypeClasses, DoAndIfThenElse, FlexibleContexts #-}

module Language.SecreC.TypeChecker.SBV where

import Data.SBV hiding ((<+>))
import qualified Data.SBV as SBV

import Data.Generics
import Data.IORef
import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as Map

import Control.Monad.State as State
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer
import Control.Monad.Trans.Control
import Control.Monad.Except
import Control.Monad.Base
import Control.Monad.Catch as Catch

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Index
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint hiding (proveWith)
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Error
import Language.SecreC.Vars
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Position

import Text.PrettyPrint

import System.IO

instance MonadBase IO Symbolic where
    liftBase = liftIO

instance MonadBaseControl IO Symbolic where
    type StM Symbolic a = Symbolic a
    liftBaseWith f = liftIO $ f return
    restoreM       = id

hyp2SBV :: (VarsIdTcM loc Symbolic,Location loc) => loc -> ICond -> TcSBV loc ()
hyp2SBV l c = do
    (inHyp,_) <- State.get
    State.modify $ \(_,st) -> (True,st)
    h <- cond2SBV l c
    State.modify $ \(_,st) -> (inHyp,st)
    lift $ lift $ constrain h

proveWithTcSBV :: (MonadIO m,Location loc) => SMTConfig -> TcSBV loc SBool -> TcM loc m ThmResult
proveWithTcSBV cfg m = proveWithTcM cfg $ evalStateT m (False,Map.empty)

proveWithTcM :: (MonadIO m,Location loc) => SMTConfig -> TcM loc Symbolic SBool -> TcM loc m ThmResult
proveWithTcM cfg m = do
    arr <- Reader.ask
    env <- State.get
    st <- liftIO $ newIORef (error "proveWithTcM")
    opts <- TcM $ lift Reader.ask
    let sym = do
        e <- runSecrecMWith opts $ execTcM m arr env
        case e of
            Left err -> do
                liftIO $ writeIORef st $ Left err
                return false
            Right ((b,env'),warns) -> do
                liftIO $ writeIORef st $ Right (env',warns)
                return b
    res <- liftIO $ proveWith cfg sym
    e <- liftIO $ readIORef st
    case e of
        Left err -> throwError err
        Right (env',warns) -> do
            State.put env'
            TcM $ lift $ tell warns
    return res

type TcSBV loc = StateT (Bool,SBVals) (TcM loc Symbolic)

data SBVal where
    SBool :: SBool -> SBVal
    SInt8 :: SInt8 -> SBVal
    SInt16 :: SInt16 -> SBVal
    SInt32 :: SInt32 -> SBVal
    SInt64 :: SInt64 -> SBVal
    SWord8 :: SWord8 -> SBVal
    SWord16 :: SWord16 -> SBVal
    SWord32 :: SWord32 -> SBVal
    SWord64 :: SWord64 -> SBVal
    SFloat :: SFloat -> SBVal
    SDouble :: SDouble -> SBVal
    SLit :: Literal () -> SBVal
  deriving (Show)

instance PP SBVal where
    pp = text . show

unifiesSBVal :: Monad m => loc -> SBVal -> SBVal -> m (SBVal,SBVal)
unifiesSBVal l (SLit (BoolLit _ b1)) (SBool b2) = return (SBool $ fromBool b1,SBool b2)
unifiesSBVal l (SBool b1) (SLit (BoolLit _ b2)) = return (SBool b1,SBool $ fromBool b2)
unifiesSBVal l (SBool b1) (SBool b2) = return (SBool b1,SBool b2)
unifiesSBVal l (SLit (IntLit _ b1)) (SInt8 b2) = return (SInt8 $ literal $ fromInteger b1,SInt8 b2)
unifiesSBVal l (SInt8 b1) (SLit (IntLit _ b2)) = return (SInt8 b1,SInt8 $ literal $ fromInteger b2)
unifiesSBVal l (SInt8 b1) (SInt8 b2) = return (SInt8 b1,SInt8 b2)
unifiesSBVal l (SLit (IntLit _ b1)) (SInt16 b2) = return (SInt16 $ literal $ fromInteger b1,SInt16 b2)
unifiesSBVal l (SInt16 b1) (SLit (IntLit _ b2)) = return (SInt16 b1,SInt16 $ literal $ fromInteger b2)
unifiesSBVal l (SInt16 b1) (SInt16 b2) = return (SInt16 b1,SInt16 b2)
unifiesSBVal l (SLit (IntLit _ b1)) (SInt32 b2) = return (SInt32 $ literal $ fromInteger b1,SInt32 b2)
unifiesSBVal l (SInt32 b1) (SLit (IntLit _ b2)) = return (SInt32 b1,SInt32 $ literal $ fromInteger b2)
unifiesSBVal l (SInt32 b1) (SInt32 b2) = return (SInt32 b1,SInt32 b2)
unifiesSBVal l (SLit (IntLit _ b1)) (SInt64 b2) = return (SInt64 $ literal $ fromInteger b1,SInt64 b2)
unifiesSBVal l (SInt64 b1) (SLit (IntLit _ b2)) = return (SInt64 b1,SInt64 $ literal $ fromInteger b2)
unifiesSBVal l (SInt64 b1) (SInt64 b2) = return (SInt64 b1,SInt64 b2)
unifiesSBVal l (SWord8 b1) (SLit (IntLit _ b2)) = return (SWord8 b1,SWord8 $ literal $ fromInteger b2)
unifiesSBVal l (SWord8 b1) (SWord8 b2) = return (SWord8 b1,SWord8 b2)
unifiesSBVal l (SLit (IntLit _ b1)) (SWord16 b2) = return (SWord16 $ literal $ fromInteger b1,SWord16 b2)
unifiesSBVal l (SWord16 b1) (SLit (IntLit _ b2)) = return (SWord16 b1,SWord16 $ literal $ fromInteger b2)
unifiesSBVal l (SWord16 b1) (SWord16 b2) = return (SWord16 b1,SWord16 b2)
unifiesSBVal l (SLit (IntLit _ b1)) (SWord32 b2) = return (SWord32 $ literal $ fromInteger b1,SWord32 b2)
unifiesSBVal l (SWord32 b1) (SLit (IntLit _ b2)) = return (SWord32 b1,SWord32 $ literal $ fromInteger b2)
unifiesSBVal l (SWord32 b1) (SWord32 b2) = return (SWord32 b1,SWord32 b2)
unifiesSBVal l (SLit (IntLit _ b1)) (SWord64 b2) = return (SWord64 $ literal $ fromInteger b1,SWord64 b2)
unifiesSBVal l (SWord64 b1) (SLit (IntLit _ b2)) = return (SWord64 b1,SWord64 $ literal $ fromInteger b2)
unifiesSBVal l (SWord64 b1) (SWord64 b2) = return (SWord64 b1,SWord64 b2)
unifiesSBVal l x y = return (x,y)

type SBVals = Map VarIdentifier SBVal

cond2SBV :: (VarsIdTcM loc Symbolic,Location loc) => loc -> ICond -> TcSBV loc SBool
cond2SBV l ex = case ex of
    IBool b -> return $ fromBool b
    IBInd v -> tryResolveICondVar l v
    INot e -> liftM bnot $ cond2SBV l e
    IAnd e -> liftM bAnd $ mapM (cond2SBV l) e
    IBoolOp op e1 e2 -> do
        b1 <- cond2SBV l e1
        b2 <- cond2SBV l e2
        return $ bOp2SBV op b1 b2
    ILeq e1 e2 -> do
        x <- expr2SBV l e1
        y <- expr2SBV l e2
        (x',y') <- unifiesSBVal l x y
        sbvLe l x' y'
    IEq e1 e2 -> do
        x <- expr2SBV l e1
        y <- expr2SBV l e2
        (x',y') <- unifiesSBVal l x y
        sbvEq l x' y'

expr2SBV :: (VarsIdTcM loc Symbolic,Location loc) => loc -> IExpr -> TcSBV loc SBVal
expr2SBV l ex = case ex of 
    IInt n -> return $ SLit $ IntLit () n
    IIdx v -> tryResolveIExprVar l v
    IArith op e1 e2 -> do
        x1 <- expr2SBV l e1
        x2 <- expr2SBV l e2
        (x1',x2') <- unifiesSBVal l x1 x2
        aOp2SBV l op x1' x2'
    ISym e -> do
        let x = SLit $ IntLit () (-1)
        y <- expr2SBV l e
        (x',y') <- unifiesSBVal l x y
        aOp2SBV l ITimes x' y'
  where
    aux [e] = expr2SBV l e
    aux (e:es) = do
        x <- expr2SBV l e
        y <- aux es
        (x',y') <- unifiesSBVal l x y
        sbvPlus l x' y'
    aux es = lift $ tcError (locpos l) $ NotSupportedIndexOp (parens $ sepBy comma $ map pp es) $ Just $ GenericError (locpos l) $ text "<expr2Y>"

sbvEq :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBool
sbvEq l (SInt8 x)   (SInt8 y)   = return $   (x .== y)
sbvEq l (SInt16 x)  (SInt16 y)  = return $  (x .== y)
sbvEq l (SInt32 x)  (SInt32 y)  = return $  (x .== y)
sbvEq l (SInt64 x)  (SInt64 y)  = return $  (x .== y)
sbvEq l (SWord8 x)  (SWord8 y)  = return $  (x .== y)
sbvEq l (SWord16 x) (SWord16 y) = return $ (x .== y)
sbvEq l (SWord32 x) (SWord32 y) = return $ (x .== y)
sbvEq l (SWord64 x) (SWord64 y) = return $ (x .== y)
sbvEq l (SFloat x)  (SFloat y)  = return $  (x .== y)
sbvEq l (SDouble x) (SDouble y) = return $ (x .== y)
sbvEq l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ fromBool $ i1 == i2
sbvEq l (SLit (BoolLit _ i1)) (SLit (BoolLit _ i2)) = return $ fromBool $ i1 == i2
sbvEq l (SLit (FloatLit _ i1)) (SLit (FloatLit _ i2)) = return $ fromBool $ i1 == i2
sbvEq l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> text "==" <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvEq>"

sbvLe :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBool
sbvLe l (SInt8 x)   (SInt8 y)   = return $   (x .<= y)
sbvLe l (SInt16 x)  (SInt16 y)  = return $  (x .<= y)
sbvLe l (SInt32 x)  (SInt32 y)  = return $  (x .<= y)
sbvLe l (SInt64 x)  (SInt64 y)  = return $  (x .<= y)
sbvLe l (SWord8 x)  (SWord8 y)  = return $  (x .<= y)
sbvLe l (SWord16 x) (SWord16 y) = return $ (x .<= y)
sbvLe l (SWord32 x) (SWord32 y) = return $ (x .<= y)
sbvLe l (SWord64 x) (SWord64 y) = return $ (x .<= y)
sbvLe l (SFloat x)  (SFloat y)  = return $  (x .<= y)
sbvLe l (SDouble x) (SDouble y) = return $ (x .<= y)
sbvLe l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ fromBool $ i1 <= i2
sbvLe l (SLit (BoolLit _ i1)) (SLit (BoolLit _ i2)) = return $ fromBool $ i1 <= i2
sbvLe l (SLit (FloatLit _ i1)) (SLit (FloatLit _ i2)) = return $ fromBool $ i1 <= i2
sbvLe l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> text "<=" <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvLe>"

sbvPlus :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBVal
sbvPlus l (SInt8 x)   (SInt8 y)   = return $ SInt8   (x + y)
sbvPlus l (SInt16 x)  (SInt16 y)  = return $ SInt16  (x + y)
sbvPlus l (SInt32 x)  (SInt32 y)  = return $ SInt32  (x + y)
sbvPlus l (SInt64 x)  (SInt64 y)  = return $ SInt64  (x + y)
sbvPlus l (SWord8 x)  (SWord8 y)  = return $ SWord8  (x + y)
sbvPlus l (SWord16 x) (SWord16 y) = return $ SWord16 (x + y)
sbvPlus l (SWord32 x) (SWord32 y) = return $ SWord32 (x + y)
sbvPlus l (SWord64 x) (SWord64 y) = return $ SWord64 (x + y)
sbvPlus l (SFloat x)  (SFloat y)  = return $ SFloat  (x + y)
sbvPlus l (SDouble x) (SDouble y) = return $ SDouble (x + y)
sbvPlus l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ IntLit () $ i1 + i2
sbvPlus l (SLit (FloatLit _ i1)) (SLit (FloatLit _ i2)) = return $ SLit $ FloatLit () $ i1 + i2
sbvPlus l (SLit (IntLit _ i1)) (SLit (FloatLit _ i2)) = return $ SLit $ FloatLit () $ realToFrac i1 + i2
sbvPlus l (SLit (FloatLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ FloatLit () $ i1 + realToFrac i2
sbvPlus l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> char '+' <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvPlus>"

sbvMinus :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBVal
sbvMinus l (SInt8 x)   (SInt8 y)   = return $ SInt8   (x - y)
sbvMinus l (SInt16 x)  (SInt16 y)  = return $ SInt16  (x - y)
sbvMinus l (SInt32 x)  (SInt32 y)  = return $ SInt32  (x - y)
sbvMinus l (SInt64 x)  (SInt64 y)  = return $ SInt64  (x - y)
sbvMinus l (SWord8 x)  (SWord8 y)  = return $ SWord8  (x - y)
sbvMinus l (SWord16 x) (SWord16 y) = return $ SWord16 (x - y)
sbvMinus l (SWord32 x) (SWord32 y) = return $ SWord32 (x - y)
sbvMinus l (SWord64 x) (SWord64 y) = return $ SWord64 (x - y)
sbvMinus l (SFloat x)  (SFloat y)  = return $ SFloat  (x - y)
sbvMinus l (SDouble x) (SDouble y) = return $ SDouble (x - y)
sbvMinus l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ IntLit () $ i1 - i2
sbvMinus l (SLit (FloatLit _ i1)) (SLit (FloatLit _ i2)) = return $ SLit $ FloatLit () $ i1 - i2
sbvMinus l (SLit (IntLit _ i1)) (SLit (FloatLit _ i2)) = return $ SLit $ FloatLit () $ realToFrac i1 - i2
sbvMinus l (SLit (FloatLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ FloatLit () $ i1 - realToFrac i2
sbvMinus l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> char '+' <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvMinus>"

sbvTimes :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBVal
sbvTimes l (SInt8 x)   (SInt8 y)   = return $ SInt8   (x * y)
sbvTimes l (SInt16 x)  (SInt16 y)  = return $ SInt16  (x * y)
sbvTimes l (SInt32 x)  (SInt32 y)  = return $ SInt32  (x * y)
sbvTimes l (SInt64 x)  (SInt64 y)  = return $ SInt64  (x * y)
sbvTimes l (SWord8 x)  (SWord8 y)  = return $ SWord8  (x * y)
sbvTimes l (SWord16 x) (SWord16 y) = return $ SWord16 (x * y)
sbvTimes l (SWord32 x) (SWord32 y) = return $ SWord32 (x * y)
sbvTimes l (SWord64 x) (SWord64 y) = return $ SWord64 (x * y)
sbvTimes l (SFloat x)  (SFloat y)  = return $ SFloat  (x * y)
sbvTimes l (SDouble x) (SDouble y) = return $ SDouble (x * y)
sbvTimes l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ IntLit () $ i1 * i2
sbvTimes l (SLit (FloatLit _ i1)) (SLit (FloatLit _ i2)) = return $ SLit $ FloatLit () $ i1 * i2
sbvTimes l (SLit (IntLit _ i1)) (SLit (FloatLit _ i2)) = return $ SLit $ FloatLit () $ realToFrac i1 * i2
sbvTimes l (SLit (FloatLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ FloatLit () $ i1 * realToFrac i2
sbvTimes l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> char '+' <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvTimes>"

sbvPower :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBVal
sbvPower l (SInt8 x)   (SInt8 y)   = return $ SInt8   (x .^ y)
sbvPower l (SInt16 x)  (SInt16 y)  = return $ SInt16  (x .^ y)
sbvPower l (SInt32 x)  (SInt32 y)  = return $ SInt32  (x .^ y)
sbvPower l (SInt64 x)  (SInt64 y)  = return $ SInt64  (x .^ y)
sbvPower l (SWord8 x)  (SWord8 y)  = return $ SWord8  (x .^ y)
sbvPower l (SWord16 x) (SWord16 y) = return $ SWord16 (x .^ y)
sbvPower l (SWord32 x) (SWord32 y) = return $ SWord32 (x .^ y)
sbvPower l (SWord64 x) (SWord64 y) = return $ SWord64 (x .^ y)
sbvPower l (SFloat x)  (SInt8 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SInt16 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SInt32 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SInt64 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SWord8 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SWord16 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SWord32 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SWord64 y)  = return $ SFloat  (x .^ y)
sbvPower l (SFloat x)  (SLit (IntLit _ i2))  = return $ SFloat  (x .^ (fromInteger i2::SInteger))
sbvPower l (SDouble x)  (SInt8 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SInt16 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SInt32 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SInt64 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SWord8 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SWord16 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SWord32 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SWord64 y)  = return $ SDouble  (x .^ y)
sbvPower l (SDouble x)  (SLit (IntLit _ i2))  = return $ SDouble  (x .^ (fromInteger i2::SInteger))
sbvPower l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ IntLit () $ i1 ^ i2
sbvPower l (SLit (FloatLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ FloatLit () $ i1 ^^ i2
sbvPower l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> char '+' <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvPower>"

sbvDiv :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBVal
sbvDiv l (SInt8 x)   (SInt8 y)   = return $ SInt8   (x `sDiv` y)
sbvDiv l (SInt16 x)  (SInt16 y)  = return $ SInt16  (x `sDiv` y)
sbvDiv l (SInt32 x)  (SInt32 y)  = return $ SInt32  (x `sDiv` y)
sbvDiv l (SInt64 x)  (SInt64 y)  = return $ SInt64  (x `sDiv` y)
sbvDiv l (SWord8 x)  (SWord8 y)  = return $ SWord8  (x `sDiv` y)
sbvDiv l (SWord16 x) (SWord16 y) = return $ SWord16 (x `sDiv` y)
sbvDiv l (SWord32 x) (SWord32 y) = return $ SWord32 (x `sDiv` y)
sbvDiv l (SWord64 x) (SWord64 y) = return $ SWord64 (x `sDiv` y)
sbvDiv l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ IntLit () $ i1 `div` i2
sbvDiv l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> char '+' <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvDiv>"

sbvMod :: Location loc => loc -> SBVal -> SBVal -> TcSBV loc SBVal
sbvMod l (SInt8 x)   (SInt8 y)   = return $ SInt8   (x `sMod` y)
sbvMod l (SInt16 x)  (SInt16 y)  = return $ SInt16  (x `sMod` y)
sbvMod l (SInt32 x)  (SInt32 y)  = return $ SInt32  (x `sMod` y)
sbvMod l (SInt64 x)  (SInt64 y)  = return $ SInt64  (x `sMod` y)
sbvMod l (SWord8 x)  (SWord8 y)  = return $ SWord8  (x `sMod` y)
sbvMod l (SWord16 x) (SWord16 y) = return $ SWord16 (x `sMod` y)
sbvMod l (SWord32 x) (SWord32 y) = return $ SWord32 (x `sMod` y)
sbvMod l (SWord64 x) (SWord64 y) = return $ SWord64 (x `sMod` y)
sbvMod l (SLit (IntLit _ i1)) (SLit (IntLit _ i2)) = return $ SLit $ IntLit () $ i1 `mod` i2
sbvMod l x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp x <+> char '+' <+> pp y) $ Just $ GenericError (locpos l) $ text "<sbvMod>"

aOp2SBV :: Location loc => loc -> IAOp -> SBVal -> SBVal -> TcSBV loc SBVal
aOp2SBV l IPlus x y = sbvPlus l x y
aOp2SBV l IMinus x y = sbvMinus l x y
aOp2SBV l ITimes x y = sbvTimes l x y
aOp2SBV l IPower x y = sbvPower l x y
aOp2SBV l IDiv x y = sbvDiv l x y
aOp2SBV l IModOp x y = sbvMod l x y
--aOp2SBV l op x y = lift $ tcError (locpos l) $ NotSupportedIndexOp (pp op <+> pp x <+> pp y) $ Just $ GenericError (locpos l) $ text "<aOp2SBV>"

bOp2SBV :: Boolean b => IBOp -> b -> b -> b
bOp2SBV IOr = (|||)
bOp2SBV IXor = (SBV.<+>)

sbVal :: String -> Prim -> Symbolic SBVal
sbVal v (DatatypeBool      _) = liftM SBool $ sBool v
sbVal v (DatatypeInt8      _) = liftM SInt8 $ sInt8 v
sbVal v (DatatypeUint8     _) = liftM SWord8 $ sWord8 v
sbVal v (DatatypeInt16     _) = liftM SInt16 $ sInt16 v
sbVal v (DatatypeUint16    _) = liftM SWord16 $ sWord16 v
sbVal v (DatatypeInt32     _) = liftM SInt32 $ sInt32 v
sbVal v (DatatypeUint32    _) = liftM SWord32 $ sWord32 v
sbVal v (DatatypeInt64     _) = liftM SInt64 $ sInt64 v
sbVal v (DatatypeUint64    _) = liftM SWord64 $ sWord64 v
sbVal v (DatatypeXorUint8  _) = liftM SWord8 $ sWord8 v
sbVal v (DatatypeXorUint16 _) = liftM SWord16 $ sWord16 v
sbVal v (DatatypeXorUint32 _) = liftM SWord32 $ sWord32 v
sbVal v (DatatypeXorUint64 _) = liftM SWord64 $ sWord64 v
sbVal v (DatatypeFloat32   _) = liftM SFloat $ sFloat v
sbVal v (DatatypeFloat64   _) = liftM SDouble $ sDouble v

tryResolveIExprVar :: (VarsIdTcM loc Symbolic,Location loc) => loc -> VarName VarIdentifier Prim -> TcSBV loc SBVal
tryResolveIExprVar l v@(VarName t n) = do
    mb <- lift $ tryResolveEVar l n (BaseT $ TyPrim t)
    case mb of
        Just e -> lift (expr2IExpr e) >>= expr2SBV l
        Nothing -> do
            (inHyp,sbvs) <- State.get
            case Map.lookup n sbvs of
                Just i -> return i
                Nothing -> do
                    unless inHyp $ lift $ addErrorM l Halt $ tcError (locpos l) $ UnresolvedVariable (pp n)
                    i <- lift $ lift $ sbVal (ppr v) t
                    State.modify $ \(inHyp,sbvs) -> (inHyp,Map.insert n i sbvs)
                    return i

tryResolveICondVar :: (VarsIdTcM loc Symbolic,Location loc) => loc -> VarIdentifier -> TcSBV loc SBool
tryResolveICondVar l n = do
    mb <- lift $ tryResolveEVar l n (BaseT bool)
    case mb of
        Just e -> lift (expr2ICond e) >>= cond2SBV l
        Nothing -> do
            (inHyp,sbvs) <- State.get
            case Map.lookup n sbvs of
                Just (SBool b) -> return b
                Just x -> lift $ genTcError (locpos l) $ text "not a SBool" <+> pp x
                Nothing -> do
                    unless inHyp $ lift $ addErrorM l Halt $ tcError (locpos l) $ UnresolvedVariable (pp n)
                    b <- lift $ lift $ sBool (ppr n)
                    State.modify $ \(inHyp,sbvs) -> (inHyp,Map.insert n (SBool b) sbvs)
                    return b
