module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint

import Data.Traversable
import Data.Maybe
import Data.Monoid
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.List as List

import Control.Monad hiding (mapM)
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State

import Prelude hiding (mapM)

tcTypeSpec :: Location loc => TypeSpecifier loc -> TcM loc (TypeSpecifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) = do
    (sec',tsec) <- tcMbSecTypeSpec sec 
    dta' <- tcDatatypeSpec dta
    let tdta = typed $ loc dta'
    (dim',tdim) <- tcMbDimtypeSpec dim
    let t = CType tsec tdta tdim [] -- return type without array sizes
    return $ TypeSpecifier (Typed l t) sec' dta' dim'
    
tcMbSecTypeSpec :: Location loc => Maybe (SecTypeSpecifier loc) -> TcM loc (Maybe (SecTypeSpecifier (Typed loc)),Type)
tcMbSecTypeSpec Nothing = return (Nothing,Public) -- public by default
tcMbSecTypeSpec (Just sec) = do
    sec' <- tcReaderM $ tcSecTypeSpec sec
    let t = typed $ loc sec'
    return (Just sec',t)

tcSecTypeSpec :: Location loc => SecTypeSpecifier loc -> TcReaderM loc (SecTypeSpecifier (Typed loc))
tcSecTypeSpec (PublicSpecifier l) = do
    return $ PublicSpecifier (Typed l Public)
tcSecTypeSpec (PrivateSpecifier l d) = do
    t <- checkPrivateDomain d
    let d' = fmap (flip Typed t) d
    return $ PrivateSpecifier (Typed l t) d'

tcDatatypeSpec :: Location loc => DatatypeSpecifier loc -> TcM loc (DatatypeSpecifier (Typed loc))
tcDatatypeSpec (PrimitiveSpecifier l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveSpecifier (Typed l t) p'
tcDatatypeSpec tplt@(TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM tcTemplateTypeArgument args
    let ts = map (typed . loc) args'
    ret <- tcCstrM l $ TApp tn ts
    dec <- tcCstrM l $ TDec tn ts
    let n' = fmap (flip Typed dec) n
    return $ TemplateSpecifier (Typed l ret) n' args'
tcDatatypeSpec (VariableSpecifier l v) = do
    t <- tcReaderM $ checkNonTemplateType v
    let v' = fmap (flip Typed t) v 
    return $ VariableSpecifier (Typed l t) v'

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = PrimType $ fmap (const ()) p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: Location loc => TemplateTypeArgument loc -> TcM loc (TemplateTypeArgument (Typed loc))
tcTemplateTypeArgument (GenericTemplateTypeArgument l n) = do
    t <- tcReaderM $ checkTemplateArg n
    let n' = fmap (flip Typed t) n
    return $ GenericTemplateTypeArgument (Typed l t) n'
tcTemplateTypeArgument (TemplateTemplateTypeArgument l n args) = do
    TemplateSpecifier l' n' args' <- tcDatatypeSpec (TemplateSpecifier l n args)
    return $ TemplateTemplateTypeArgument l' n' args'
tcTemplateTypeArgument (PrimitiveTemplateTypeArgument l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveTemplateTypeArgument (Typed l t) p'
tcTemplateTypeArgument (IntTemplateTypeArgument l i) = do
    let t = TDim i
    return $ IntTemplateTypeArgument (Typed l t) i
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = Public
    return $ PublicTemplateTypeArgument (Typed l t)

tcMbDimtypeSpec :: Location loc => Maybe (DimtypeSpecifier loc) -> TcM loc (Maybe (DimtypeSpecifier (Typed loc)),Expression ())
tcMbDimtypeSpec Nothing = return (Nothing,integerExpr 0) -- 0 by default
tcMbDimtypeSpec (Just dim) = do
    (dim',t) <- tcDimtypeSpec dim
    return (Just dim',t)

tcDimtypeSpec :: Location loc => DimtypeSpecifier loc -> TcM loc (DimtypeSpecifier (Typed loc),Expression ())
tcDimtypeSpec (DimSpecifier l e) = do
    e' <- tcDimSizeExpr Nothing e
    return (DimSpecifier (notTyped l) e',fmap (const ()) e') 

tcRetTypeSpec :: Location loc => ReturnTypeSpecifier loc -> TcM loc (ReturnTypeSpecifier (Typed loc))
tcRetTypeSpec (ReturnType l Nothing) = do
    let t = Void
    return $ ReturnType (Typed l Void) Nothing
tcRetTypeSpec (ReturnType l (Just s)) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    return $ ReturnType (Typed l t) (Just s')

-- | Retrieves a constant dimension from a type
typeDim :: Location loc => loc -> Type -> TcM loc (Maybe Integer)
typeDim l (CType _ _ e _) = do
    let le = fmap (const noloc) e
    (_,mb) <- uintLitExpr le
    when (isNothing mb) $ tcWarn (locpos l) $ NoStaticDimension (fmap locpos le)
    return mb
typeDim l _ = error "no dimension"

projectMatrixType :: Location loc => loc -> Type -> [(Maybe Integer,Maybe Integer)] -> TcProofM loc Type
projectMatrixType l (CType sec t dim szs) rngs = do
    mb <- lift $ isStaticUintExpr dim
    case mb of
        Nothing -> tcError (locpos l) $ NonStaticDimension
        Just d -> do
            if (d > 0 && length szs >= length rngs)
                then do
                    szs' <- projectSizes l szs rngs
                    return $ CType sec t (integerExpr $ toEnum $ length szs') szs'
                else tcError (locpos l) $ MismatchingArrayDimension (toEnum $ length szs) (toEnum $ length rngs) Nothing
projectMatrisType l (TK k) rngs = do -- resolve templates
    ret <- resolveTCstr l k
    projectMatrixType l ret rngs

projectSizes :: Location loc => loc -> [Expression ()] -> [(Maybe Integer,Maybe Integer)] -> TcProofM loc [Expression ()]
projectSizes l [] _ = return []
projectSizes l _ [] = return []
projectSizes l (x:xs) (y:ys) = do
    mb <- lift $ isStaticUintExpr x
    z <- case mb of
        Just sz -> do
            let low = maybe 0 id (fst y)
                upp = maybe sz id (snd y)
            if (sz >= low && sz <= upp)
                then return $ integerExpr (upp - low)
                else tcError (locpos l) $ ArrayAccessOutOfBounds sz (low,upp)
        otherwise -> do
            tcWarn (locpos l) $ DependentSizeSelection
            return x
    zs <- projectSizes l xs ys
    return (z:zs)

-- | checks that a given type is a struct type, resolving struct templates if necessary, and projects a particular field.
projectStructField :: Location loc => loc -> Type -> AttributeName () -> TcProofM loc Type
projectStructField l (StructType _ _ atts) (AttributeName _ a) = do -- project the field
    case List.find (\(Attribute _ t f) -> attributeNameId f == a) atts of
        Nothing -> tcError (locpos l) $ FieldNotFound a
        Just (Attribute _ t f) -> return $ typeSpecifierLoc t
projectStructField l (TK k) a = do -- resolve templates
    ret <- resolveTCstr l k
    projectStructField l ret a

castType :: Location loc => loc -> Type -> Type -> TcProofM loc Type
castType = error "cast" -- TODO