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
import Language.SecreC.TypeChecker.Environment

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

typeToSecType :: (Vars loc,Location loc) => loc -> Type -> TcM loc SecType
typeToSecType l (SecT s) = return s
typeToSecType l t = genericError (locpos l) $ text "Expected a security type but found" <+> quotes (pp t)

typeToDecType :: (Vars loc,Location loc) => loc -> Type -> TcM loc DecType
typeToDecType l (DecT s) = return s
typeToDecType l t = genericError (locpos l) $ text "Expected a declaration type but found" <+> quotes (pp t)

typeToBaseType :: (Vars loc,Location loc) => loc -> Type -> TcM loc BaseType
typeToBaseType l (BaseT s) = return s
typeToBaseType l t@(ComplexT ct@(CType s b d sz)) = do
    tcCstrM l $ Equals t (ComplexT $ CType Public b (indexExpr 0) [])
    return b
typeToBaseType l t = genericError (locpos l) $ text "Expected a base type but found" <+> quotes (text $ show t)

typeToComplexType :: (Vars loc,Location loc) => loc -> Type -> TcM loc ComplexType
typeToComplexType l (ComplexT s) = return s
typeToComplexType l (BaseT s) = return $ defCType s
typeToComplexType l t = genericError (locpos l) $ text "Expected a complex type but found" <+> quotes (pp t)

tcTypeSpec :: (Vars loc,Location loc) => TypeSpecifier Identifier loc -> TcM loc (TypeSpecifier VarIdentifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) = do
    (sec',tsec) <- tcMbSecTypeSpec sec 
    (dta',tdta) <- tcDatatypeSpecBase dta
    (dim',tdim) <- tcMbDimtypeSpec (pp tsec <+> pp tdta) dim
    let t = ComplexT $ CType tsec tdta (fmap typed tdim) [] -- return type without array sizes
    return $ TypeSpecifier (Typed l t) sec' dta' dim'
    
tcMbSecTypeSpec :: (Vars loc,Location loc) => Maybe (SecTypeSpecifier Identifier loc) -> TcM loc (Maybe (SecTypeSpecifier VarIdentifier (Typed loc)),SecType)
tcMbSecTypeSpec Nothing = return (Nothing,Public) -- public by default
tcMbSecTypeSpec (Just sec) = do
    sec' <- tcSecTypeSpec sec
    let t = typed $ loc sec'
    s <- typeToSecType (unTyped $ loc sec') t
    return (Just sec',s)

tcSecTypeSpec :: (Vars loc,Location loc) => SecTypeSpecifier Identifier loc -> TcM loc (SecTypeSpecifier VarIdentifier (Typed loc))
tcSecTypeSpec (PublicSpecifier l) = do
    return $ PublicSpecifier (Typed l $ SecT Public)
tcSecTypeSpec (PrivateSpecifier l d) = do
    let vd = bimap mkVarId id d
    t <- checkDomain vd
    let d' = fmap (flip Typed t) vd
    return $ PrivateSpecifier (Typed l t) d'

tcDatatypeSpecBase :: (Vars loc,Location loc) => DatatypeSpecifier Identifier loc -> TcM loc (DatatypeSpecifier VarIdentifier (Typed loc),BaseType)
tcDatatypeSpecBase d = do
    d' <- tcDatatypeSpec d
    let tdta = typed $ loc d'
    t <- typeToBaseType (unTyped $ loc d') tdta
    return (d',t)

tcDatatypeSpec :: (Vars loc,Location loc) => DatatypeSpecifier Identifier loc -> TcM loc (DatatypeSpecifier VarIdentifier (Typed loc))
tcDatatypeSpec (PrimitiveSpecifier l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveSpecifier (Typed l t) p'
tcDatatypeSpec tplt@(TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM tcTemplateTypeArgument args
    let ts = map (typed . loc) args'
    let vn = bimap mkVarId id n
    ret <- tcTopCstrM l $ TApp (fmap (const ()) vn) ts
    dec <- tcTopCstrM l $ TDec (fmap (const ()) vn) ts
    let n' = fmap (flip Typed dec) vn
    return $ TemplateSpecifier (Typed l ret) n' args'
tcDatatypeSpec (VariableSpecifier l v) = do
    let vv = bimap mkVarId id v
    t <- checkNonTemplateType vv
    let v' = fmap (flip Typed t) vv 
    return $ VariableSpecifier (Typed l t) v'

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = BaseT $ TyPrim $ fmap (const ()) p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: (Vars loc,Location loc) => TemplateTypeArgument Identifier loc -> TcM loc (TemplateTypeArgument VarIdentifier (Typed loc))
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
tcTemplateTypeArgument (ExprTemplateTypeArgument l e) = do
    e' <- tcExpr e
    let t = IdxT $ fmap (typed) e'
    return $ ExprTemplateTypeArgument (Typed l t) e'
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = SecT $ Public
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
    return $ ReturnType (Typed l $ ComplexT Void) Nothing
tcRetTypeSpec (ReturnType l (Just s)) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    return $ ReturnType (Typed l t) (Just s')

-- | Retrieves a constant dimension from a type
typeDim :: (Vars loc,Location loc) => loc -> ComplexType -> TcM loc (Maybe Word64)
typeDim l ct@(CType _ _ e _) = do
    let le = fmap (Typed l) e
    mb <- tryEvalIndexExpr le
    case mb of
        Left err -> do
            tcWarn (locpos l) $ NoStaticDimension (pp ct) err
            return Nothing
        Right w -> return (Just w)
typeDim l t = genericError (locpos l) $ text "No dimension for type" <+> pp t

projectMatrixType :: (Vars loc,Location loc) => loc -> ComplexType -> [ArrayProj] -> TcM loc ComplexType
projectMatrixType l ct rngs = do
    let err = TypecheckerError (locpos l) . UnresolvedMatrixProjection (pp ct) (brackets $ ppArrayRanges rngs)
    addErrorM err (projectMatrixCType l ct rngs)
  where
    projectMatrixCType :: (Vars loc,Location loc) => loc -> ComplexType -> [ArrayProj] -> TcM loc ComplexType
    projectMatrixCType l ct@(CType sec t dim szs) rngs = do
        szs' <- resolveSizes l dim szs
        mb <- tryEvalIndexExpr (fmap (Typed l) dim)
        case mb of
            Left err -> tcError (locpos l) $ NonStaticDimension (pp ct) err
            Right d -> do
                szs'' <- projectSizes l ct 1 szs' rngs  
                return $ CType sec t (indexExpr $ toEnum $ length szs'') szs''
    projectMatrixCType l (CVar v) rngs = do
        t <- resolveCVar l v
        projectMatrixCType l t rngs

projectSizes :: (Vars loc,Location loc) => loc -> ComplexType -> Word64 -> [Expression VarIdentifier Type] -> [ArrayProj] -> TcM loc [Expression VarIdentifier Type]
projectSizes p ct i xs [] = return xs
projectSizes p ct i [] ys = tcError (locpos p) $ MismatchingArrayDimension (pp ct) i (i + toEnum (length ys)) (Left $ brackets $ ppArrayRanges ys)
projectSizes p ct i (x:xs) (ArrayIdx y:ys) = do
    projectSize p ct i x y y
    projectSizes p ct (succ i) xs ys
projectSizes p ct i (x:xs) (ArraySlice y1 y2:ys) = do
    z <- projectSize p ct i x y1 y2
    zs <- projectSizes p ct (succ i) xs ys
    return (z:zs)

projectSize :: (Vars loc,Location loc) => loc -> ComplexType -> Word64 -> Expression VarIdentifier Type -> ArrayIndex -> ArrayIndex -> TcM loc (Expression VarIdentifier Type)
projectSize p ct i x y1 y2 = do
    mb <- tryEvalIndexExpr (fmap (Typed p) x)
    let low = case y1 of
                NoArrayIndex -> StaticArrayIndex 0
                i -> i
    let upp = case y2 of
                NoArrayIndex -> either (DynArrayIndex x) (StaticArrayIndex) mb
                i -> i
    let arrerr = case maybeToList (arrayIndexErr low) ++ maybeToList (arrayIndexErr upp) ++ either (:[]) (const []) mb of
                    [] -> GenericError (locpos p) $ text "Unknown"
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
projectStructField :: (Vars loc,Location loc) => loc -> DecType -> AttributeName VarIdentifier () -> TcM loc Type
projectStructField l (StructType _ _ atts) (AttributeName _ a) = do -- project the field
    case List.find (\(Attribute _ t f) -> attributeNameId f == a) atts of
        Nothing -> tcError (locpos l) $ FieldNotFound (pp a)
        Just (Attribute _ t f) -> return $ typeSpecifierLoc t

resolveSizes :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc [Expression VarIdentifier Type]
resolveSizes l d [] = do
    i <- evalIndexExpr $ fmap (Typed l) d
    replicateM (fromEnum i) newSizeVar
resolveSizes l d xs = return xs

subtractIndexExprs :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc (Expression VarIdentifier Type)
subtractIndexExprs l e1 e2@(LitPExpr _ (IntLit _ 0)) = return e1
subtractIndexExprs l e1@(LitPExpr l1 (IntLit l2 i1)) e2@(LitPExpr _ (IntLit _ i2)) = return $ LitPExpr l1 $ IntLit l2 (i1 - i2)
subtractIndexExprs l e1 e2 = do
    dec <- resolveTCstr l $ PDec (Right $ OpSub ()) [BaseT index,BaseT index] (BaseT index)
    return $ BinaryExpr (BaseT index) e1 (OpSub dec) e2

isZeroTypeExpr :: (Vars loc,Location loc) => loc -> Expression VarIdentifier Type -> TcM loc Bool
isZeroTypeExpr l e = do
    let e' = fmap (Typed l) e
    mb <- tryEvalIndexExpr e'
    case mb of
        Right 0 -> return True
        otherwise -> return False     
    
-- | Update the size of a compound type
refineTypeSizes :: (Vars loc,Location loc) => loc -> ComplexType -> Maybe (Sizes VarIdentifier Type) -> TcM loc ComplexType
refineTypeSizes l ct@(CType s t d sz) Nothing = do
    return ct
refineTypeSizes l ct@(CType s t d []) (Just (Sizes szs)) = do
    let tsz = Foldable.toList szs
--    unifiesSizes l d sz d tsz
    return $ CType s t d tsz
refineTypeSizes l ct _ = genericError (locpos l) $ text "Expected a complex type but found" <+> pp ct
