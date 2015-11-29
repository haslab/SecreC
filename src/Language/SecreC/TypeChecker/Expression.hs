{-# LANGUAGE DataKinds, TypeFamilies #-}

module Language.SecreC.TypeChecker.Expression where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Position
import Language.SecreC.Location
import Language.SecreC.Pretty
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Statement
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Semantics
import Language.SecreC.Vars
import Language.SecreC.Utils

import Prelude hiding (mapM)

import Control.Monad hiding (mapAndUnzipM,mapM)
import Control.Monad.IO.Class

import Data.Bifunctor
import Data.Monoid
import Data.Maybe
import Data.Traversable
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import Data.Int
import Data.Word

import Text.PrettyPrint

tcGuard :: (Vars loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcGuard e = tcExprTy bool e

tcExpr :: (Vars loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcExpr (BinaryAssign l pe op e) = do
    pe' <- tcExpr pe
    e' <- tcExpr e
    op' <- tcBinaryAssignOp l op (typed $ loc pe') (typed $ loc e')
    return $ BinaryAssign (notTyped l) pe' op' e'
tcExpr (QualExpr l e t) = do
    e' <- tcExpr e
    t' <- tcTypeSpec t
    tcCstrM l $ Unifies (typed $ loc t') (typed $ loc e')
    return $ QualExpr (Typed l $ typed $ loc t') e' t'
tcExpr (CondExpr l c e1 e2) = do
    c' <- tcGuard c
    e1' <- tcExpr e1
    let t1 = typed $ loc e1'
    e2' <- tcExpr e2
    let t2 = typed $ loc e2'
    tcCstrM l $ Unifies t2 t1
    return $ CondExpr (Typed l t2) c' e1' e2'
tcExpr (BinaryExpr l e1 op e2) = do
    e1' <- tcExpr e1
    e2' <- tcExpr e2
    let t1 = typed $ loc e1'
    let t2 = typed $ loc e2'
    let cop = fmap (const ()) op
    v <- newTyVar
    dec <- tcCstrM l $ PDec (Right cop) [t1,t2] v
    return $ BinaryExpr (Typed l v) e1' (fmap (flip Typed dec) op) e2'
tcExpr (CastExpr l p e) = do
    e' <- tcExpr e
    let te = typed $ loc e'
    (ret,p') <- tcCast p te
    return $ CastExpr (Typed l ret) p' e'
tcExpr (PreOp l op e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    (t',op') <- tcBinaryOp l op t t
    return $ PreOp (Typed l t') op' e'
tcExpr (PostOp l op e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    (t',op') <- tcBinaryOp l op t t
    return $ PostOp (Typed l t') op' e'
tcExpr (UnaryExpr l op e) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    v <- newTyVar
    let cop = fmap (const ()) op
    dec <- tcCstrM l $ PDec (Right cop) [t] v
    return $ UnaryExpr (Typed l v) (fmap (flip Typed dec) op) e'
tcExpr (DomainIdExpr l s) = do
    s' <- tcSecTypeSpec s
    let t = typed $ loc s'
    return $ DomainIdExpr (Typed l t) s'
tcExpr (StringFromBytesExpr l e) = do
    e' <- tcExprTy bytes e
    return $ StringFromBytesExpr (Typed l string) e'
tcExpr (BytesFromStringExpr l e) = do
    e' <- tcExprTy string e
    return $ BytesFromStringExpr (Typed l bytes) e'
tcExpr call@(ProcCallExpr l n@(ProcedureName pl pn) es) = do
    let vn = bimap mkVarId id n
    es' <- mapM tcExpr es
    let ts = map (typed . loc) es'
    v <- newTyVar
    dec <- tcCstrM l $ PDec (Left $ fmap (const ()) vn) ts v -- we don't know the return type on application
    return $ ProcCallExpr (Typed l v) (fmap (flip Typed dec) vn) es'
tcExpr (PostIndexExpr l e s) = do
    e' <- tcExpr e
    let t = typed $ loc e'
    (s',t') <- tcSubscript t s
    return $ PostIndexExpr (Typed l t') e' s'
tcExpr (SelectionExpr l pe a) = do
    let va = bimap mkVarId id a
    pe' <- tcExpr pe
    let tpe' = typed $ loc pe'
    t <- tcCstrM l $ ProjectStruct tpe' (fmap (const ()) va)
    return $ SelectionExpr (Typed l t) pe' (fmap notTyped va)
tcExpr (ArrayConstructorPExpr l es) = error "tcExpr" -- TODO
tcExpr (RVariablePExpr l v) = do
    v' <- tcVarName v
    let t = typed $ loc v'
    return $ RVariablePExpr (Typed l t) v'
tcExpr (LitPExpr l lit) = do
    lit' <- tcLiteral lit
    let tlit = typed $ loc lit'
    return $ LitPExpr (Typed l tlit) lit'

-- special handling for arrays: cast its inner elements
tcCast :: Location loc => CastType Identifier loc -> Type -> TcM loc (Type,CastType VarIdentifier (Typed loc))
tcCast (CastPrim l p) te = do
    p' <- tcPrimitiveDatatype p
    let bp = typed $ loc p'
    (dec,to) <- tcCastTy l bp te
    return $ (to,CastPrim (Typed l dec) p')
tcCast (CastTy l v) te = do
    v' <- tcTypeName v
    let bp = typed $ loc v'
    (dec,to) <- tcCastTy l bp te
    return $ (to,CastTy (Typed l dec) v')

tcCastTy :: Location loc => loc -> Type -> Type -> TcM loc (Type,Type)
tcCastTy l bto from = do
    bfrom <- tcCstrM l $ GetCBase from
    dec <- tcCstrM l $ Cast bfrom bto
    to <- tcCstrM l $ SetCBase from bto
    return (dec,to)

tcBinaryAssignOp :: Location loc => loc -> BinaryAssignOp loc -> Type -> Type -> TcM loc (BinaryAssignOp (Typed loc))
tcBinaryAssignOp l bop t1 t2 = do 
    let mb_op = binAssignOpToOp bop
    dec <- case mb_op of
        Just op -> tcCstrM l $ PDec (Right op) [t1,t2] t1
        Nothing -> tcCstrM l $ Unifies t1 t2
    return (fmap (flip Typed dec) bop)
    
tcBinaryOp :: (Vars loc,Location loc) => loc -> Op loc -> Type -> Type -> TcM loc (Type,Op (Typed loc))
tcBinaryOp l op t1 t2 = do 
    v <- newTyVar
    let cop = fmap (const ()) op
    dec <- tcCstrM l $ PDec (Right cop) [t1,t2] v
    return (v,fmap (flip Typed dec) op)

-- | Selects a list of indices from a type, and returns the type of the selection
tcSubscript :: (Vars loc,Location loc) => Type -> Subscript Identifier loc -> TcM loc (Subscript VarIdentifier (Typed loc),Type)
tcSubscript t s = do
    let l = loc s
    (s',rngs) <- mapAndUnzipM tcIndex s
    ret <- tcCstrM l $ ProjectMatrix t (Foldable.toList rngs)
    return (s',ret)

tcIndex :: (Vars loc,Location loc) => Index Identifier loc -> TcM loc (Index VarIdentifier (Typed loc),ArrayProj)
tcIndex (IndexInt l e) = do
    (e',mb) <- tcIndexExpr e
    let ei = case mb of
                Left err -> DynArrayIndex (fmap typed e') err
                Right i -> StaticArrayIndex i
    return (IndexInt (notTyped l) e',ArrayIdx ei)
tcIndex (IndexSlice l e1 e2) = do
    let f x = case x of
                Nothing -> (Nothing,NoArrayIndex)
                Just (y,Left err) -> (Just y,DynArrayIndex (fmap typed y) err)
                Just (y,Right i) -> (Just y,StaticArrayIndex i)
    (e1',mb1) <- liftM f $ mapM tcIndexExpr e1
    (e2',mb2) <- liftM f $ mapM tcIndexExpr e2
    return (IndexSlice (notTyped l) e1' e2',ArraySlice mb1 mb2)

tcLiteral :: Location loc => Literal loc -> TcM loc (Literal (Typed loc))
tcLiteral (IntLit l i) = do
    let lit = IntLit () i
    v <- newTyVar
    bv <- tcCstrM l $ GetCBase v
    tcCstrM l $ Coerces (TyLit lit) bv
    return $ IntLit (Typed l v) i
tcLiteral (StringLit l s) = do
    let lit = StringLit () s
    v <- newTyVar
    bv <- tcCstrM l $ GetCBase v
    tcCstrM l $ Coerces (TyLit lit) bv
    return $ StringLit (Typed l v) s
tcLiteral (BoolLit l b) = do
    let lit = BoolLit () b
    v <- newTyVar
    bv <- tcCstrM l $ GetCBase v
    tcCstrM l $ Coerces (TyLit lit) bv
    return $ BoolLit (Typed l v) b
tcLiteral (FloatLit l f) = do
    let lit = FloatLit () f
    v <- newTyVar
    bv <- tcCstrM l $ GetCBase v
    tcCstrM l $ Coerces (TyLit lit) bv
    return $ FloatLit (Typed l v) f

tcVarName :: Location loc => VarName Identifier loc -> TcM loc (VarName VarIdentifier (Typed loc))
tcVarName v@(VarName l n) = do
    t <- checkVariable LocalScope $ bimap mkVarId id v
    return $ VarName (Typed l t) $ mkVarId n

tcTypeName :: Location loc => TypeName Identifier loc -> TcM loc (TypeName VarIdentifier (Typed loc))
tcTypeName v@(TypeName l n) = do
    t <- checkNonTemplateType (bimap mkVarId id v)
    return $ TypeName (Typed l t) (mkVarId n)

-- | returns the operation performed by a binary assignment operation
binAssignOpToOp :: BinaryAssignOp loc -> Maybe (Op ())
binAssignOpToOp (BinaryAssignEqual _) = Nothing
binAssignOpToOp (BinaryAssignMul _) = Just $ OpMul ()
binAssignOpToOp (BinaryAssignDiv _) = Just $ OpDiv ()
binAssignOpToOp (BinaryAssignMod _) = Just $ OpMod ()
binAssignOpToOp (BinaryAssignAdd _) = Just $ OpAdd ()
binAssignOpToOp (BinaryAssignSub _) = Just $ OpSub ()
binAssignOpToOp (BinaryAssignAnd _) = Just $ OpBand ()
binAssignOpToOp (BinaryAssignOr _)  = Just $ OpBor ()
binAssignOpToOp (BinaryAssignXor _) = Just $ OpXor ()

-- | typechecks an expression and tries to evaluate it to an index
tcIndexExpr :: (Vars loc,Location loc) => Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc),Either SecrecError Word64)
tcIndexExpr e = do
    e' <- tcExprTy index e
    mb <- tryEvalIndexExpr e'
    return (e',mb)

tcExprTy :: (Vars loc,Location loc) => Type -> Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcExprTy ty e = do
    e' <- tcExpr e
    let Typed l ty' = loc e'
    tcCstrM l $ Unifies ty' ty
    return e'

tcDimExpr :: (Vars loc,Location loc) => Doc -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcDimExpr doc v sz = do
    (sz',mb) <- tcIndexExpr sz
    let ty = typed $ loc sz'
    -- size must be a value of the longest unsigned int
    tcCstrM (loc sz) $ Unifies ty index
    -- check if size is static and if so evaluate it
    case mb of
        Left err -> tcWarn (locpos $ loc sz') $ DependentMatrixDimension doc (pp sz') (fmap pp v) err
        Right _ -> return ()
    return sz'     
    
tcSizeExpr :: (Vars loc,Location loc) => Type -> Word64 -> Maybe (VarName Identifier loc) -> Expression Identifier loc -> TcM loc (Expression VarIdentifier (Typed loc))
tcSizeExpr t i v sz = do
    (sz',mb) <- tcIndexExpr sz
    let ty = typed $ loc sz'
    -- size must be a value of the longest unsigned int
    tcCstrM (loc sz) $ Unifies ty index
    -- check if size is static and if so evaluate it
    case mb of
        Left err -> tcWarn (locpos $ loc sz') $ DependentMatrixSize (pp t) i (pp sz') (fmap pp v) err
        Right _ -> return ()
    return sz'     








