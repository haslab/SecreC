{-# LANGUAGE ViewPatterns, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Index where

import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars

import Text.PrettyPrint

import Control.Monad.Except

import Data.List

import Safe

isIndexType :: Type -> Bool
isIndexType t = isIntType t || isBoolType t

expr2ICondOrExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either ICond IExpr)
expr2ICondOrExpr e = do
    let (Typed l t) = loc e
    addErrorM l (TypecheckerError (locpos l) . NotSupportedIndexOp (pp e) . Just) $ do
        isICond <- isBoolTypeM l t 
        if isICond
            then liftM Left (expr2ICond e)
            else liftM Right (expr2IExpr e)

expr2IExprAs :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> Type -> TcM loc m (IExpr)
expr2IExprAs e t = do
    let l = unTyped $ loc e
    i <- expr2IExpr e
    addErrorM l (TypecheckerError (locpos l) . NotSupportedIndexOp (pp e) . Just) $ do
        ok <- isIntTypeM l t
        unless ok $ genTcError noloc $ text "Not an index type:" <+> pp t
        return i

expr2IExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (IExpr)
expr2IExpr e@(RVariablePExpr _ (VarName (Typed l t) n)) = do
    mb <- tryResolveEVar l n t
    case mb of
        Just e' -> expr2IExpr e'
        Nothing -> addErrorM l (TypecheckerError (locpos l) . NotSupportedIndexOp (pp e) . Just) $ do
            p <- typeToPrimType l t
            if isNumericPrimType p
                then return $ IIdx $ VarName p n
                else genTcError noloc $ text "Not an index type:" <+> pp t
expr2IExpr (LitPExpr _ (IntLit _ i)) = return $ IInt i
expr2IExpr (QualExpr l e t) = expr2IExpr $ updLoc e (flip Typed (typed $ loc t) $ unTyped $ loc e)
expr2IExpr (UnaryExpr _ (OpSub _) e) = liftM ISym $ expr2IExpr e
expr2IExpr (BinaryExpr _ e1 op e2) = do
    i1 <- expr2IExpr e1
    i2 <- expr2IExpr e2
    mapEOp op i1 i2
expr2IExpr ce@(UnaryExpr _ (OpCast _ t) e) = do
    let l = unTyped $ loc ce
    i <- expr2IExpr e
    addErrorM l (TypecheckerError (locpos l) . NotSupportedIndexOp (pp e) . Just) $ do
        let ty = typed $ loc t
        p <- typeToPrimType l ty
        if isNumericPrimType p
            then return i
            else genTcError (locpos l) $ text "Unsupported cast"
expr2IExpr (ProcCallExpr l (ProcedureName _ ((==mkVarId "size") -> True)) Nothing [(e,False)]) = do
    let t = typed $ loc e
    let ll = unTyped l
    sz <- prove ll "expr2IExpr size" $ typeSize ll t
    expr2IExpr $ fmap (Typed ll) sz
expr2IExpr pe@(ProcCallExpr l pn@(ProcedureName _ ((==mkVarId "product") -> True)) Nothing [(RVariablePExpr t v,isVariadic)]) = do
    let ll = unTyped l
    mb <- tryResolveEVar ll (varNameId v) (typed t)
    case mb of
        Just e' -> expr2IExpr $ (ProcCallExpr l pn Nothing [(e',isVariadic)])
        otherwise -> tcError (locpos $ unTyped $ loc pe) $ NotSupportedIndexOp (pp pe) Nothing
expr2IExpr (ProcCallExpr l (ProcedureName _ ((==mkVarId "product") -> True)) Nothing [(ArrayConstructorPExpr _ es,_)]) = do
    is <- mapM expr2IExpr es
    return $ iProduct is
expr2IExpr e = tcError (locpos $ unTyped $ loc e) $ NotSupportedIndexOp (pp e) Nothing

mapEOp :: (MonadIO m,PP id,Location loc) => Op id (Typed loc) -> IExpr -> IExpr -> TcM loc m (IExpr)
mapEOp (OpAdd _) x y = return $ x .+. y
mapEOp (OpSub _) x y = return $ x .-. y
mapEOp (OpMul _) x y = return $ x .*. y
mapEOp (OpDiv _)   x y = return $ x ./. y
--mapAOp ModOp x y = return $ x .%. y
--mapAOp Power x y = return $ x .**. y
mapEOp o x y = tcError (locpos $ unTyped $ loc o) $ NotSupportedIndexOp (pp o) Nothing

expr2ICond :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (ICond)
expr2ICond e@(RVariablePExpr _ (VarName (Typed l t) n)) = do
    mb <- tryResolveEVar l n t
    case mb of
        Just e' -> expr2ICond e'
        Nothing -> addErrorM l (TypecheckerError (locpos l) . NotSupportedIndexOp (pp e) . Just) $ do
            ok <- isBoolTypeM l t
            if ok
                then return $ IBInd n
                else genTcError noloc $ text "Not an index condition type:" <+> pp t
expr2ICond (LitPExpr _ (BoolLit _ b)) = return $ IBool b
expr2ICond (QualExpr l e t) = expr2ICond $ updLoc e (flip Typed (typed $ loc t) $ unTyped $ loc e)
expr2ICond (UnaryExpr _ (OpNot _) e) = liftM INot $ expr2ICond e
expr2ICond (BinaryExpr _ e1 op@(isCmpOp -> True) e2) = do
    i1 <- expr2IExpr e1
    i2 <- expr2IExpr e2
    mapCOp op i1 i2
expr2ICond (BinaryExpr _ e1 op@(isBoolOp -> True) e2) = do
    i1 <- expr2ICond e1
    i2 <- expr2ICond e2
    mapBOp op i1 i2
expr2ICond e = tcError (locpos $ unTyped $ loc e) $ NotSupportedIndexOp (pp e) Nothing

mapCOp :: (MonadIO m,Location loc,PP id) => Op id (Typed loc) -> IExpr -> IExpr -> TcM loc m (ICond)
mapCOp (OpEq _) x y = return $ x .==. y
mapCOp (OpNe _) x y = return $ x ./=. y
mapCOp (OpLt _) x y = return $ x .<. y
mapCOp (OpLe _) x y = return $ x .<=. y
mapCOp (OpGt _) x y = return $ x .>. y
mapCOp (OpGe _) x y = return $ x .>=. y
mapCOp o x y = tcError (locpos $ unTyped $ loc o) $ NotSupportedIndexOp (pp o) Nothing

mapBOp :: (MonadIO m,Location loc,PP id) => Op id (Typed loc) -> ICond -> ICond -> TcM loc m (ICond)
mapBOp (OpLor _) x y = return $ x .||. y
mapBOp (OpXor _) x y = return $ x .^^. y
mapBOp (OpLand _) x y = return $ x .&&. y
mapBOp o x y = tcError (locpos $ unTyped $ loc o) $ NotSupportedIndexOp (pp o) Nothing

tryExpr2IExpr :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either (IExpr) SecrecError)
tryExpr2IExpr e = liftM Left (expr2IExpr e) `catchError` (return . Right)

tryExpr2ICond :: (VarsIdTcM loc m,Location loc) => Expression VarIdentifier (Typed loc) -> TcM loc m (Either (ICond) SecrecError)
tryExpr2ICond e = liftM Left (expr2ICond e) `catchError` (return . Right)

--------------------------------------------------------------------------------
-- * Syntactic sugar

iProduct :: [IExpr] -> IExpr
iProduct [] = IInt 0
iProduct [x] = x
iProduct (x:xs) = x .*. iProduct xs

(.+.), (.-.), (.*.), (.**.), (./.), (.%.) :: IExpr -> IExpr -> IExpr
(.+.)  = IArith IPlus
(.-.)  = IArith IMinus
(.*.)  = IArith ITimes
(.**.) = IArith IPower
(./.)  = IArith IDiv
(.%.)  = IArith IModOp

(.==.), (./=.), (.<.), (.<=.), (.>.), (.>=.) :: IExpr -> IExpr -> ICond
(.==.) e1 e2 = IEq e1 e2
(./=.) e1 e2 = INot (e1 .==. e2)
(.<.)  e1 e2 = IAnd [ILeq e1 e2,e1 ./=. e2] -- we don't resort to arithmetic because of possible overflows
(.<=.) e1 e2 = ILeq e1 e2
(.>.)  = flip (.<.)
(.>=.) = flip (.<=.)

(.||.), (.^^.),(.&&.),sameBool :: ICond -> ICond -> ICond
(.||.) = IBoolOp IOr
(.^^.) = IBoolOp IXor
(.&&.) x y = IAnd [x,y]
sameBool = \c1 c2 -> INot $ IBoolOp IXor c1 c2

implies :: ICond -> ICond -> ICond
implies p q = (INot p) .||. q

-- * Simplifying index expressions

--------------------------------------------------------------------------------
-- This implements the properties of the several boolean operators,
-- except conjuntion. It does not use equality on expressions, only
-- on variables.
truthTable :: ICond -> ICond
truthTable (IBoolOp op (IBool b1) (IBool b2)) 
    = IBool $ mapIBOp op b1 b2
truthTable (IBoolOp IOr (IBool b1) b2)
    | b1 = IBool True
    | otherwise = truthTable b2
truthTable (IBoolOp IOr b1 (IBool b2))
    | b2 = IBool True
    | otherwise = truthTable b1
truthTable (IBoolOp IXor (IBool b1) b2)
    | b1 = truthTable $ deMorgan b2
    | otherwise = truthTable b2
truthTable (IBoolOp IXor b1 (IBool b2))
    | b2 = truthTable $ deMorgan b1
    | otherwise = truthTable b1
truthTable (IBoolOp IXor (IBInd b1) (IBInd b2))
    | b1 == b2 = IBool False
    | otherwise = IBool True
truthTable (IBoolOp _ (IBInd b1) (IBInd b2)) -- Idempotence
    | b1 == b2 = IBInd b1
truthTable e = e

--------------------------------------------------------------------------------
-- Application of deMorgan rules
deMorgan :: ICond -> ICond
deMorgan (IBool b)            = IBool $ not b
deMorgan (INot c)             = c
deMorgan (IBoolOp IOr c1 c2)  = IAnd [deMorgan c1, deMorgan c2]
deMorgan (IBoolOp IXor c1 c2) = aux c1 c2
    where
    aux (IBool b) e   = IBoolOp IXor (IBool $ not b) e
    aux e (IBool b)   = IBoolOp IXor e (IBool $ not b)
    aux (INot b) e    = IBoolOp IXor b e
    aux e (INot b)    = IBoolOp IXor e b
    aux i@(IBInd _) e = IBoolOp IXor (INot i) e
    aux e i@(IBInd _) = IBoolOp IXor e (INot i)
    aux e1 e2         = IBoolOp IXor (deMorgan e1) e2
deMorgan (IAnd lc)            = andToOr $ map deMorgan lc
    where
    andToOr []        = error "<deMorgan>: unexpected case"
    andToOr [x]       = x
    andToOr (x:xs)    = IBoolOp IOr x (andToOr xs)
deMorgan i                    = INot i

--------------------------------------------------------------------------------
evalICond :: ICond -> ICond

evalICond (INot c) = case deMorgan (evalICond c) of
    IAnd l -> flatAnd l
    c'     -> truthTable c'

evalICond (IAnd l) = flatAnd $ map evalICond l
-- Canonical form for Nested expressions
evalICond (IBoolOp op c1 c2) = case (evalICond c1, evalICond c2) of
    (l1@(IAnd _), l2) -> flatAnd $ distrOr l1 l2
    (l1, l2@(IAnd _)) -> flatAnd $ distrOr l1 l2
    (l1, l2)          -> truthTable $ IBoolOp op l1 l2

evalICond (ILeq e1 e2) = case (evalIExpr e1,evalIExpr e2) of
    (IInt i1,IInt i2) -> IBool $ i1 <= i2
    (e1',e2')     -> ILeq e1' e2'

evalICond (IEq e1 e2)  = case (evalIExpr e1,evalIExpr e2) of
    (IInt i1,IInt i2) -> IBool $ i1 == i2
    (e1',e2')     -> IEq e1' e2'

evalICond c = c

--------------------------------------------------------------------------------
distrOr :: ICond -> ICond -> [ICond]
distrOr (IAnd l1) (IAnd l2) = concatMap (distrOr' l1) l2
distrOr c (IAnd l2) = distrOr' l2 c
distrOr (IAnd l1) c = distrOr' l1 c
distrOr _ _ = error "<distrOr>: not expected"

distrOr' :: [ICond] -> ICond -> [ICond]
distrOr' l c = map (IBoolOp IOr c) l

--------------------------------------------------------------------------------
-- Remove True
-- Reduce to False
-- Bring out nested And
flatAnd :: [ICond] -> ICond
flatAnd c = let
        (v, var, i) = foldr aux (True, [], []) c
    in if v && not (null i && null var) 
        then IAnd (nub var ++ i) 
        else IBool v

    where
    aux (IBool False) _     = (False, [], [])
    aux (IBool True)  r     = r
    aux (IAnd l) (v, vs, r) = case flatAnd l of
        IAnd l'     -> (v, vs, l' ++ r)
        IBool False -> (False, [], [])
        IBool True  -> (v, vs, r)
        _ -> error "flatAnd.aux: Not expected case"
    aux i@(IBInd _) (v, vs, r) = (v, i : vs, r)
    aux x        (v, vs, r) = case truthTable x of
        IBool False -> (False, [], [])
        IBool True  -> (v, vs, r)
        x'          -> (v, vs, x' : r)

evalIExpr :: IExpr -> IExpr
evalIExpr = id

--------------------------------------------------------------------------------
mapIBOp :: IBOp -> Bool -> Bool -> Bool
mapIBOp IOr  = (||)
mapIBOp IXor = (/=)

--------------------------------------------------------------------------------
mapIAOp :: IAOp -> Integer -> Integer -> Integer
mapIAOp IMinus = (-)
mapIAOp ITimes = (*)
mapIAOp IPower = (^)
mapIAOp IDiv   = div
mapIAOp IModOp = mod

-- | simplify a set of conditions according to a set of hypotheses
fromHyp :: [ICond] -> [ICond] -> ICond
fromHyp hyp cond = let
        cond' = filter (not . checkHyp hyp) cond
    in if null cond' then IBool True else IAnd cond'

    where

    checkHyp :: [ICond] -> ICond -> Bool
    checkHyp hyp' c = any (exactHyp c) hyp'

    exactHyp :: ICond -> ICond -> Bool
-- C, a |= a
    exactHyp c h
        | c == h = True
    exactHyp c (IAnd l) = checkHyp l c
    exactHyp _ _ = False

evalBool :: [ICond] -> Bool
evalBool = toBool . evalICond . IAnd
toBool :: ICond -> Bool
toBool (IBool b) = b
toBool _ = False 




