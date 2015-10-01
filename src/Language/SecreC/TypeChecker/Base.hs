{-# LANGUAGE FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Base where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils

import Data.Generics
import qualified Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad.Reader

-- warn for unused local variables

data TcEnv loc = TcEnv {
      globalVars :: Map Identifier (VarEnv loc)
    , localVars  :: Map Identifier (VarEnv loc)
    }
  deriving Functor

emptyTcEnv :: TcEnv loc
emptyTcEnv = TcEnv Map.empty Map.empty 

data VarEnv loc = VarEnv {
      varLoc :: loc -- ^ Location where the variable is defined
    , varType :: Type -- ^ Type of the variable
    , varInit :: Maybe (Expression (Typed loc)) -- ^ Optional initialization expression
    }
  deriving Functor

type TcM loc = StateT (TcEnv loc) SecrecM

type TcReaderM loc = ReaderT (TcEnv loc) SecrecM

tcReaderM :: TcReaderM loc a -> TcM loc a
tcReaderM r = do
    s <- get
    lift $ runReaderT r s

tcLocM :: (loc2 -> loc1) -> (loc1 -> loc2) -> TcM loc1 a -> TcM loc2 a
tcLocM f g m = do
    s2 <- get
    (x,s1) <- lift $ runStateT m (fmap f s2)
    put (fmap g s1)
    return x

-- | Typechecks a code block, with local declarations only within its scope
tcBlock :: TcM loc a -> TcM loc a
tcBlock m = do
    s <- get
    lift $ evalStateT m s

runTcM :: TcM loc a -> SecrecM a
runTcM m = evalStateT m emptyTcEnv

data Type
    = NoType -- ^ For locations with no associated type information
    | Void -- ^ Empty type
    | StmtType (Set StmtClass) -- ^ Type of a @Statement@
    | CType -- ^ Compound SecreC type
        SecurityType -- ^ security type
        Type -- ^ data type
        Int -- ^ dimension (default = 0, i.e., scalars)
        (Maybe (NeList (Expression Position))) -- ^ sizes for each dimension (dependent types?) -- NOTE: check bounds if size is statically known?
    | PrimType (PrimitiveDatatype ())
  deriving (Read,Show,Data,Typeable,Eq,Ord)

refineTypeSizes :: Location loc => Type -> Maybe (Sizes loc) -> Type
refineTypeSizes (CType s t d sz) Nothing = CType s t d Nothing
refineTypeSizes (CType s t d sz) (Just ss) = let Sizes sz' = fmap locpos ss in CType s t d $ Just sz'
refineTypeSizes _ _ = error "no size"

typeDim :: Type -> Int
typeDim (CType _ _ d _) = d
typeDim _ = error "no dimension"

typeBase :: Type -> Type
typeBase (CType _ b _ _) = b
typeBase _ = error "no base"

data SecurityType
    = Public
    | Private Identifier Identifier
  deriving (Read,Show,Data,Typeable,Eq,Ord)

data StmtClass
    -- | The execution of the statement may end because of reaching a return statement
    = StmtReturn Type
    -- | The execution of the statement may end because of reaching a break statement
    | StmtBreak
    -- | The execution of the statement may end because of reaching a continue statement
    | StmtContinue
    -- | The execution of the statement may end without reaching a return, break or continue statement
    | StmtFallthru
  deriving (Read,Show,Data,Typeable,Eq,Ord)

isLoopStmtClass :: StmtClass -> Bool
isLoopStmtClass c = List.elem c [StmtBreak,StmtContinue]

isLoopBreakStmtClass :: StmtClass -> Bool
isLoopBreakStmtClass StmtBreak = True
isLoopBreakStmtClass (StmtReturn _) = True
isLoopBreakStmtClass _ = False

isIterationStmtClass :: StmtClass -> Bool
isIterationStmtClass c = List.elem c [StmtContinue,StmtFallthru]

data Typed a = Typed a Type
  deriving (Read,Show,Data,Typeable,Functor)

instance Located loc => Located (Typed loc) where
    type (LocOf (Typed loc)) = LocOf loc
    loc = loc . unTyped
    
instance Location a => Location (Typed a) where
    locpos = locpos . unTyped

notTyped :: a -> Typed a
notTyped x = Typed x NoType

unTyped :: Typed a -> a
unTyped (Typed a t) = a

locType :: Typed Position -> Type
locType (Typed _ t) = t

typeLoc :: Type -> Position -> Typed Position
typeLoc t l = Typed l t

noTypeLoc :: Loc loc a -> Loc (Typed loc) a
noTypeLoc = mapLoc (flip Typed NoType)

coerces :: loc -> Type -> Type -> TcReaderM loc ()
coerces = undefined


