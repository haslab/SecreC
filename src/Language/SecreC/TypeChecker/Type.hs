{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Base hiding (int)
import Language.SecreC.TypeChecker.Semantics
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint

import Data.Bifunctor
import Data.Traversable
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.List as List
import Data.Int
import Data.Word
import qualified Data.Foldable as Foldable

import Control.Monad hiding (mapM)
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.State (State(..),StateT(..))
import qualified Control.Monad.State as State
import Control.Monad.Reader (Reader(..),ReaderT(..))
import qualified Control.Monad.Reader as Reader
import Control.Monad.Except

import Text.PrettyPrint as PP

import Prelude hiding (mapM)

tcTypeSpec :: (Vars loc,Location loc) => TypeSpecifier Identifier loc -> TcM loc (TypeSpecifier VarIdentifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) = do
    (sec',tsec) <- tcMbSecTypeSpec sec 
    dta' <- tcDatatypeSpec dta
    let tdta = typed $ loc dta'
    (dim',tdim) <- tcMbDimtypeSpec (pp tsec <+> pp tdta) dim
    let t = CType tsec tdta (fmap typed tdim) [] -- return type without array sizes
    return $ TypeSpecifier (Typed l t) sec' dta' dim'
    
tcMbSecTypeSpec :: Location loc => Maybe (SecTypeSpecifier Identifier loc) -> TcM loc (Maybe (SecTypeSpecifier VarIdentifier (Typed loc)),Type)
tcMbSecTypeSpec Nothing = return (Nothing,Public) -- public by default
tcMbSecTypeSpec (Just sec) = do
    sec' <- tcSecTypeSpec sec
    let t = typed $ loc sec'
    return (Just sec',t)

tcSecTypeSpec :: Location loc => SecTypeSpecifier Identifier loc -> TcM loc (SecTypeSpecifier VarIdentifier (Typed loc))
tcSecTypeSpec (PublicSpecifier l) = do
    return $ PublicSpecifier (Typed l Public)
tcSecTypeSpec (PrivateSpecifier l d) = do
    let vd = bimap mkVarId id d
    t <- checkDomain vd
    let d' = fmap (flip Typed t) vd
    return $ PrivateSpecifier (Typed l t) d'

tcDatatypeSpec :: Location loc => DatatypeSpecifier Identifier loc -> TcM loc (DatatypeSpecifier VarIdentifier (Typed loc))
tcDatatypeSpec (PrimitiveSpecifier l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveSpecifier (Typed l t) p'
tcDatatypeSpec tplt@(TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM tcTemplateTypeArgument args
    let ts = map (typed . loc) args'
    let vn = bimap mkVarId id n
    ret <- tcCstrM l $ TApp (fmap (const ()) vn) ts
    dec <- tcCstrM l $ TDec (fmap (const ()) vn) ts
    let n' = fmap (flip Typed dec) vn
    return $ TemplateSpecifier (Typed l ret) n' args'
tcDatatypeSpec (VariableSpecifier l v) = do
    let vv = bimap mkVarId id v
    t <- checkNonTemplateType vv
    let v' = fmap (flip Typed t) vv 
    return $ VariableSpecifier (Typed l t) v'

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = PrimType $ fmap (const ()) p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: Location loc => TemplateTypeArgument Identifier loc -> TcM loc (TemplateTypeArgument VarIdentifier (Typed loc))
tcTemplateTypeArgument (GenericTemplateTypeArgument l n) = do
    let vn = bimap mkVarId id n
    t <- checkTemplateArg vn
    let n' = fmap (flip Typed t) vn
    return $ GenericTemplateTypeArgument (Typed l t) n'
tcTemplateTypeArgument (TemplateTemplateTypeArgument l n args) = do
    TemplateSpecifier l' n' args' <- tcDatatypeSpec (TemplateSpecifier l n args)
    return $ TemplateTemplateTypeArgument l' n' args'
tcTemplateTypeArgument (PrimitiveTemplateTypeArgument l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveTemplateTypeArgument (Typed l t) p'
tcTemplateTypeArgument (IntTemplateTypeArgument l i) = do
    let t = TyLit $ IntLit () i
    return $ IntTemplateTypeArgument (Typed l t) i
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = Public
    return $ PublicTemplateTypeArgument (Typed l t)

tcMbDimtypeSpec :: (Vars loc,Location loc) => Doc -> Maybe (DimtypeSpecifier Identifier loc) -> TcM loc (Maybe (DimtypeSpecifier VarIdentifier (Typed loc)),Expression VarIdentifier (Typed loc))
tcMbDimtypeSpec doc Nothing = return (Nothing,fmap (Typed noloc) (indexExpr 0)) -- 0 by default
tcMbDimtypeSpec doc (Just dim) = do
    (dim',t) <- tcDimtypeSpec doc dim
    return (Just dim',t)

tcDimtypeSpec :: (Vars loc,Location loc) => Doc -> DimtypeSpecifier Identifier loc -> TcM loc (DimtypeSpecifier VarIdentifier (Typed loc),Expression VarIdentifier (Typed loc))
tcDimtypeSpec doc (DimSpecifier l e) = do
    e' <- tcDimExpr doc Nothing e
    return (DimSpecifier (notTyped l) e',e') 

tcRetTypeSpec :: (Vars loc,Location loc) => ReturnTypeSpecifier Identifier loc -> TcM loc (ReturnTypeSpecifier VarIdentifier (Typed loc))
tcRetTypeSpec (ReturnType l Nothing) = do
    let t = Void
    return $ ReturnType (Typed l Void) Nothing
tcRetTypeSpec (ReturnType l (Just s)) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    return $ ReturnType (Typed l t) (Just s')

-- | Retrieves a constant dimension from a type
typeDim :: (Vars loc,Location loc) => loc -> Type -> TcM loc (Maybe Word64)
typeDim l ct@(CType _ _ e _) = do
    let le = fmap (Typed l) e
    mb <- tryEvalIndexExpr le
    case mb of
        Left err -> do
            tcWarn (locpos l) $ NoStaticDimension (pp ct) err
            return Nothing
        Right w -> return (Just w)
typeDim l t = genericError (locpos l) $ "no dimension for " ++ ppr t

projectMatrixType :: (Vars loc,Location loc) => loc -> Type -> [ArrayProj] -> TcM loc Type
projectMatrixType l ct rngs = (projectMatrixType' l ct rngs)
    `catchError` matrixProjectionError l ct rngs
  where
    projectMatrixType' :: (Vars loc,Location loc) => loc -> Type -> [ArrayProj] -> TcM loc Type
    projectMatrixType' l ct@(CType sec t dim szs) rngs = do
        szs' <- resolveSizes l dim szs
        mb <- tryEvalIndexExpr (fmap (Typed l) dim)
        case mb of
            Left err -> tcError (locpos l) $ NonStaticDimension (pp ct) err
            Right d -> do
                szs'' <- projectSizes l ct 1 szs' rngs  
                return $ CType sec t (indexExpr $ toEnum $ length szs'') szs''   
    projectMatrixType' l (TK k) rngs = do -- resolve templates
        ret <- resolveTCstr l k
        projectMatrixType' l ret rngs
    projectMatrixType' l (TVar v) rngs = do
        t <- resolveTVar l v
        projectMatrixType' l t rngs
    projectMatrixType' l t rngs = genericError (locpos l) "Unknown"
    
matrixProjectionError l t rngs err = tcError (locpos l) $ UnresolvedMatrixProjection (pp t) (brackets $ ppArrayRanges rngs) err

projectSizes :: (Vars loc,Location loc) => loc -> Type -> Word64 -> [Expression VarIdentifier Type] -> [ArrayProj] -> TcM loc [Expression VarIdentifier Type]
projectSizes p ct i xs [] = return xs
projectSizes p ct i [] ys = tcError (locpos p) $ MismatchingArrayDimension (pp ct) i (i + toEnum (length ys)) (Left $ brackets $ ppArrayRanges ys)
projectSizes p ct i (x:xs) (ArrayIdx y:ys) = do
    projectSize p ct i x y y
    projectSizes p ct (succ i) xs ys
projectSizes p ct i (x:xs) (ArraySlice y1 y2:ys) = do
    z <- projectSize p ct i x y1 y2
    zs <- projectSizes p ct (succ i) xs ys
    return (z:zs)

projectSize :: (Vars loc,Location loc) => loc -> Type -> Word64 -> Expression VarIdentifier Type -> ArrayIndex -> ArrayIndex -> TcM loc (Expression VarIdentifier Type)
projectSize p ct i x y1 y2 = do
    mb <- tryEvalIndexExpr (fmap (Typed p) x)
    let low = case y1 of
                NoArrayIndex -> StaticArrayIndex 0
                i -> i
    let upp = case y2 of
                NoArrayIndex -> either (DynArrayIndex x) (StaticArrayIndex) mb
                i -> i
    let arrerr = case maybeToList (arrayIndexErr low) ++ maybeToList (arrayIndexErr upp) ++ either (:[]) (const []) mb of
                    [] -> GenericError (locpos p) "Unknown"
                    x:xs -> x
    let elow = arrayIndexExpr low
    let eupp = arrayIndexExpr upp
    case (low,upp,mb) of
        (StaticArrayIndex l,StaticArrayIndex u,Right sz) ->
            if (l >= 0 && u >= 0 && sz >= l && u <= sz)
                then return $ indexExpr (u - l)
                else tcError (locpos p) $ ArrayAccessOutOfBounds (pp ct) i (pp l <> char ':' <> pp u)
        otherwise -> do
            tcWarn (locpos p) $ DependentSizeSelection (pp ct) i (Just $ pp elow <> char ':' <> pp eupp) arrerr
            subtractIndexExprs p eupp elow          

-- | checks that a given type is a struct type, resolving struct templates if necessary, and projects a particular field.
projectStructField :: (Vars loc,Location loc) => loc -> Type -> AttributeName VarIdentifier () -> TcM loc Type
projectStructField l (StructType _ _ atts) (AttributeName _ a) = do -- project the field
    case List.find (\(Attribute _ t f) -> attributeNameId f == a) atts of
        Nothing -> tcError (locpos l) $ FieldNotFound (pp a)
        Just (Attribute _ t f) -> return $ typeSpecifierLoc t
projectStructField l (TK k) a = do -- resolve templates
    ret <- resolveTCstr l k
    projectStructField l ret a

-- coerces a complex type with possible zeroed dimensions into another complex type
--coercesCType :: (Vars loc,Location loc) => loc -> Type -> Type -> TcM loc ()
--coercesCType l ct1@(CType s1 t1 dim1 szs1) ct2@(CType s2 t2 dim2 szs2) = do
--    unifies l s1 s2
--    unifies l t1 t2
--    -- no dimension coercion
--    coercesSizes l (coercesError l ct1 ct2) szs1 szs2


resolveSizes :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc [Expression VarIdentifier Type]
resolveSizes l d [] = do
    i <- evalIndexExpr $ fmap (Typed l) d
    replicateM (fromEnum i) newSizeVar
resolveSizes l d xs = return xs
    
-- accept trailing zeroes on the left side
--coercesSizes :: (Vars loc,Location loc) => loc -> TcM loc () -> [Expression VarIdentifier Type] -> [Expression VarIdentifier Type] -> TcM loc ()
--coercesSizes l err [] [] = return ()
--coercesSizes l err xs [] = mapM_ (unifiesExpr l (indexExpr 0)) xs
--               `mplus` err
--coercesSizes l err [] ys = err
--coercesSizes l err (x:xs) (y:ys) = do
--    unifiesExpr l x y
--    coercesSizes l err xs ys

---- | Eliminates trailing dimensions with zero size.
--simplifyCType :: (Vars loc,Location loc) => loc -> Type -> TcM loc Type
--simplifyCType l (CType s t dim szs) = do
--    (szs',zeroes) <- trailingM (isZeroTypeExpr l) szs
--    -- since we only use this in constraint solving functions
--    dim2 <- subtractIndexExprs l dim (LitPExpr index $ IntLit index $ toEnum $ length zeroes)
--    dim' <- liftM (fmap typed) $ simplifyIndexExpr $ fmap (Typed l) dim2
--    return $ CType s t dim' szs'
--simplifyCType l (TVar v) = do
--    mb <- tryResolveTVar l v
--    case mb of
--       Just t -> simplifyCType l t
--       Nothing -> do
--           d <- newDomainTyVar Nothing
--           t <- newTyVar
--           dim <- newDimVar 
--           let ct = CType d t dim []
--           addSubstM l v ct
--           return ct
--simplifyCType l (TK c) = resolveTK l c >>= simplifyCType l
--simplifyCType l t = genericError (locpos l) $ show $ text "Cannot simplify compound type" <+> pp t

subtractIndexExprs :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc (Expression VarIdentifier Type)
subtractIndexExprs l e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
subtractIndexExprs l e1@(LitPExpr l1 (IntLit l2 i1)) e2@(LitPExpr _ (IntLit _ i2)) = return $ LitPExpr l1 $ IntLit l2 (i1 - i2)
subtractIndexExprs l e1 e2 = do
    dec <- resolveTCstr l $ PDec (Right $ OpSub ()) [index,index] index
    return $ BinaryExpr index e1 (OpSub dec) e2

isZeroTypeExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> TcM loc Bool
isZeroTypeExpr l e = do
    let e' = fmap (Typed l) e
    mb <- tryEvalIndexExpr e'
    case mb of
        Right 0 -> return True
        otherwise -> return False     
    
-- | Update the size of a compound type
refineTypeSizes :: (Vars loc,Location loc) => loc -> Type -> Maybe (Sizes VarIdentifier Type) -> TcM loc Type
refineTypeSizes l ct@(CType s t d sz) Nothing = do
    return ct
refineTypeSizes l ct@(CType s t d []) (Just (Sizes szs)) = do
    let tsz = Foldable.toList szs
--    unifiesSizes l d sz d tsz
    return $ CType s t d tsz
refineTypeSizes l _ _ = genericError (locpos l) "not a complex type"

