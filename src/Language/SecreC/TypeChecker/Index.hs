{-# LANGUAGE ViewPatterns, FlexibleContexts #-}

module Language.SecreC.TypeChecker.Index where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Semantics
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
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
    mb <- tryResolveEVar l n
    case mb of
        Just e' -> expr2IExpr e'
        Nothing -> addErrorM l (TypecheckerError (locpos l) . NotSupportedIndexOp (pp e) . Just) $ do
            p <- typeToPrimType l t
            if isNumericPrimType p
                then return $ IIdx $ VarName p n
                else genTcError noloc $ text "Not an index type:" <+> pp t
expr2IExpr (LitPExpr _ (IntLit _ i)) = return $ IInt i
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
expr2IExpr (ProcCallExpr l (ProcedureName _ ((==mkVarId "size") -> True)) Nothing [e]) = do
    let t = typed $ loc e
    dim <- evaluateTypeSize (unTyped l) t
    return $ IInt $ toInteger dim
expr2IExpr e = do
    res <- tryEvaluateIndexExpr e
    case res of
        Left err -> tcError (locpos $ unTyped $ loc e) $ NotSupportedIndexOp (pp e) $ Just err
        Right i -> return $ IInt $ toInteger i

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
    mb <- tryResolveEVar l n
    case mb of
        Just e' -> expr2ICond e'
        Nothing -> addErrorM l (TypecheckerError (locpos l) . NotSupportedIndexOp (pp e) . Just) $ do
            ok <- isBoolTypeM l t
            if ok
                then return $ IBInd n
                else genTcError noloc $ text "Not an index condition type:" <+> pp t
expr2ICond (LitPExpr _ (BoolLit _ b)) = return $ IBool b
expr2ICond (UnaryExpr _ (OpNot _) e) = liftM INot $ expr2ICond e
expr2ICond (BinaryExpr _ e1 op@(isCmpOp -> True) e2) = do
    i1 <- expr2IExpr e1
    i2 <- expr2IExpr e2
    mapCOp op i1 i2
expr2ICond (BinaryExpr _ e1 op@(isBoolOp -> True) e2) = do
    i1 <- expr2ICond e1
    i2 <- expr2ICond e2
    mapBOp op i1 i2
expr2ICond e = do
    res <- tryEvaluateBoolExpr e
    case res of
        Left err -> tcError (locpos $ unTyped $ loc e) $ NotSupportedIndexOp (pp e) $ Just err
        Right b -> return $ IBool b

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

(.+.), (.-.), (.*.), (.**.), (./.), (.%.) :: IExpr -> IExpr -> IExpr
(.+.)  x y = ISum [x,y]
(.-.)  = IArith IMinus
(.*.)  = IArith ITimes
(.**.) = IArith IPower
(./.)  = IArith IDiv
(.%.)  = IArith IModOp

(.==.), (./=.), (.<.), (.<=.), (.>.), (.>=.) :: IExpr -> IExpr -> ICond
(.==.) e1 e2 = IEq (IArith IMinus e1 e2)
(./=.) e1 e2 = INot (e1 .==. e2)
(.<.)  e1 e2 = ILeq $ ISum [e2, ISym e1, IInt (-1)]
(.<=.) e1 e2 = ILeq $ ISum [e2, ISym e1] 
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

evalICond (ILeq e) = case evalIExpr e of
    IInt i -> IBool $ 0 <= i
    e'     -> ILeq e'

evalICond (IEq e)  = case evalIExpr e of
    IInt i -> IBool $ 0 == i
    e'     -> IEq e'

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

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Partially inspired by
-- Producing Proofs from an Arithmetic Decision Procedure in Elliptical LF
-- Aaron Stump, Clark W. Barrett, and David L. Dill

{-
 Flat form:
 1. All sums are non-empty
 2. The first element of a sum is always a constant
 3. Variables are never alone. They are always part of a product 1 * v
 4. Symmetric is moved downwards to values and variables
 5. There are not nested sums
 6. The outer symbol of a flatExpr is always a ISum
 7. Operations on literals are always computed
-}
--------------------------------------------------------------------------------
evalIExpr :: IExpr -> IExpr
evalIExpr = canonicalExpr . flatExpr

flatExpr :: IExpr -> IExpr

flatExpr i@(IInt _) = ISum [i]

flatExpr i@(IIdx _) = ISum [IInt 0, IArith ITimes (IInt 1) i]

flatExpr (ISym (IInt n)) = resInt $ negate n -- shortcut
flatExpr (ISym t) = distrSym $ flatExpr t

flatExpr (ISum l) = ISum $ flatSum $ map flatExpr l

flatExpr (IArith IMinus (IInt n) (IInt n')) = resInt $ n - n'
flatExpr (IArith IMinus (IIdx i) (IIdx i'))
    | i == i' = resInt 0
flatExpr (IArith IMinus i1 i2) =
    ISum $ flatSum [flatExpr i1, distrSym $ flatExpr i2]

flatExpr (IArith ITimes (IInt n) (IInt n')) = resInt $ n * n'
flatExpr e@(IArith ITimes _ _) = flatTimes e

flatExpr (IArith IDiv (IInt n) (IInt n')) = resInt $ div n n'
flatExpr (IArith IDiv p q) = let
        ISum p' = flatExpr p
        ISum q' = flatExpr q
    in ISum [listDiv p' q']

flatExpr (IArith IPower (IInt b) (IInt e)) = resInt $ b^e
flatExpr (IArith IPower b e) = 
    ISum [IInt 0, IArith ITimes (IInt 1) (IArith IPower (flatExpr b) (flatExpr e))]

flatExpr (IArith IModOp (IInt a) (IInt b)) = resInt $ mod a b

flatExpr e = e

resInt :: Integer -> IExpr
resInt n = ISum [IInt n]

flatTimes :: IExpr -> IExpr
flatTimes e@(IArith ITimes _ _) = let
        (ci, si, mi) = sepTimes e

        mm = toMult (product ci) mi

        (sc, ssi) = iTimesConcat $ map flatExpr si

        (pc, pe)   = iTimesLst [mm] ssi
        (pc', pe') = iTimesLst [mm] sc

        sumCi = constSum $ pc ++ pc'

    in ISum $ sumCi : pe ++ pe'
flatTimes _ = error "<flatTimes>: not expected"

toMult :: Integer -> [IExpr] -> IExpr
toMult n [] = IInt n
toMult n xs@(_:_) = IArith ITimes (IInt n) (aux xs)
    where
    aux [] = error "<toMult>: not expected"
    aux [e] = e
    aux (e:es) = IArith ITimes e (aux es)

sepTimes :: IExpr -> ([Integer], [IExpr], [IExpr])
sepTimes (IInt n) = ([n], [], [])
sepTimes i@(IIdx _) = ([], [], [i])
sepTimes s@(ISum _) = ([], [s], [])
sepTimes (IArith ITimes i1 i2) = let
        (ci1, si1, mi1) = sepTimes i1
        (ci2, si2, mi2) = sepTimes i2
    in (ci1 ++ ci2, si1 ++ si2, mi1 ++ mi2)
sepTimes (IArith IPower (IInt n) (IInt e)) = ([n ^ e], [], [])
sepTimes e@(IArith IMinus _ _) = sepTimes (flatExpr e)
sepTimes (ISym e) = sepTimes (flatExpr e)
sepTimes s@(IArith IDiv _ _) = ([], [s], [])
sepTimes _ = error "<<TODO>><sepTimes: not implemented"

constSum :: [IExpr] -> IExpr
constSum = constOp ((+), 0)

constOp :: (Integer -> Integer -> Integer, Integer) -> [IExpr] -> IExpr
constOp (f, n) = foldr aux (IInt n)
    where
    aux (IInt m) (IInt res) = IInt (f m res)
    aux _ _ = error "<constSum>: not expected"

iTimesConcat :: [IExpr] -> ([IExpr], [IExpr])
iTimesConcat [] = ([IInt 0],[IInt 1])
iTimesConcat [ISum x] = ([headNote "iTimesConcat" x], tailNote "iTimesConcat" x)
iTimesConcat (ISum x:xs) = let
        (cs, xs') = iTimesConcat xs
        (c, i)    = iTimesLst x cs
        (c', i')  = iTimesLst x xs'
    in ([constSum $ c ++ c'], i ++ i')
iTimesConcat (_:_) = error "<iTimesConcat>: not expected"

iTimesLst :: [IExpr] -> [IExpr] -> ([IExpr], [IExpr])
iTimesLst [] _ = ([], [])
iTimesLst [x] xr = let
        (nl, ol) = unzip $ map (iTimes x) xr
    in ([constSum $ concat nl], concat ol)
iTimesLst (x:xl) xr = let
        (nl, ol) = iTimesLst xl xr
        (nl', ol') = unzip $ map (iTimes x) xr
    in ([constSum (nl ++ concat nl')], ol ++ concat ol')

iTimes :: IExpr -> IExpr -> ([IExpr], [IExpr])
-- Constant * Constant
iTimes (IInt n) (IInt n') = ([IInt $ n * n'], [])
-- Constant * Variable
iTimes (IInt 0) (IIdx _) = ([], [])
iTimes (IInt n) (IIdx i) = ([], [IArith ITimes (IInt n) (IIdx i)])
iTimes (IIdx _) (IInt 0) = ([], [])
iTimes (IIdx i) (IInt n) = ([], [IArith ITimes (IInt n) (IIdx i)])
-- Constant * Product
iTimes (IInt 0) (IArith ITimes (IInt _) _) = ([], [])
iTimes (IInt n) (IArith ITimes (IInt c) i) = ([], [IArith ITimes (IInt $ c * n) i])
iTimes (IArith ITimes (IInt _) _) (IInt 0) = ([], [])
iTimes (IArith ITimes (IInt c) i) (IInt n) = ([], [IArith ITimes (IInt $ c * n) i])
-- Variable * Product
iTimes (IIdx i) (IArith ITimes (IInt c) i') = ([], [IArith ITimes (IInt c) (IArith ITimes (IIdx i) i')])
iTimes (IArith ITimes (IInt c) i') (IIdx i) = ([], [IArith ITimes (IInt c) (IArith ITimes (IIdx i) i')])
-- Product * Product
iTimes (IArith ITimes (IInt c) i) (IArith ITimes (IInt c') i') =
    ([], [IArith ITimes (IInt $ c * c') (IArith ITimes i i')]) -- TODO: Not in the right form
iTimes (IArith ITimes i1 i2) e2@(IArith ITimes _ _) =
    ([], [IArith ITimes (IInt 1) $ IArith ITimes i1 (IArith ITimes i2 e2)])
-- Produce * Division
iTimes l@(IArith IDiv _ _) r@(IInt _) = ([], [IArith ITimes l r])
iTimes l@(IInt _) r@(IArith IDiv _ _) = ([], [IArith ITimes l r])
-- Error
iTimes _ _ = error "<iTimes>: not expected"

--------------------------------------------------------------------------------
-- Expectes a flat expression
distrSym :: IExpr -> IExpr
distrSym e = case e of
    IInt n -> IInt (negate n)
    ISym i -> i

    ISum l -> ISum $ map distrSym l -- always the entry point

    IArith ITimes (IInt c) i -> IArith ITimes (IInt (negate c)) i
    IArith ITimes c _        -> IArith ITimes (distrSym c) e
    IArith IDiv (IInt c) i   -> IArith IDiv (IInt (negate c)) i
    IArith IDiv c (IInt i)   -> IArith IDiv c (IInt (negate i))
    IArith IDiv c i          -> IArith IDiv (distrSym c) i

    IArith IModOp e1 e2 ->  IArith IModOp (distrSym e1) (distrSym e2)
    IArith IPower _ _ -> error "<distrSym>: should never reach a power"
    IIdx _ -> e
    _ -> error "<<TODO>><distrSym>: missing case: "

--------------------------------------------------------------------------------

listDiv :: [IExpr] -> [IExpr] -> IExpr
listDiv [IInt l] [IInt r] = IInt $ mapIAOp IDiv l r
listDiv [IInt l] [IIdx r] = IArith IDiv (IInt l) (IIdx r)
listDiv [IIdx l] [IInt r] = IArith IDiv (IIdx l) (IInt r)
listDiv [IIdx l] [IIdx r] = IArith IDiv (IIdx l) (IIdx r)
listDiv l r = IArith IDiv (ISum l) (ISum r)

--------------------------------------------------------------------------------
-- This may not be enough to bring them to the top level
flatSum :: [IExpr] -> [IExpr]
flatSum l = let
        (c, l') = aux l
    in IInt (sum c) : concat l'
    where 
    aux :: [IExpr] -> ([Integer], [[IExpr]])
    aux [] = ([], [])
    aux (ISum (IInt n:l'):ls) = let
            (ns, ls') = aux ls
        in (n : ns, l' : ls')
    aux (ISum l':ls) = let
            (ns, ls') = aux ls
        in (ns, l' : ls')
    aux (x:ls) = let
            (ns, ls') = aux ls
        in (ns, [x]:ls')

--------------------------------------------------------------------------------
cmp :: IExpr -> IExpr -> Ordering
cmp (IInt _) _ = LT
cmp _ (IInt _) = GT
cmp (IArith ITimes (IInt _) (IIdx i)) (IArith ITimes (IInt _) (IIdx i')) =
    compare i i'
cmp (IArith op _ _) (IArith op' _ _) =
    cmpIAOp op op'
cmp (ISum _) (IArith {}) = LT
cmp (IArith {}) (ISum _) = GT
cmp (ISum l) (ISum l') = cmpList l l'
cmp _ _ = error "Ordering: not expected: "
-- Lexicographic order
cmpList :: [IExpr] -> [IExpr] -> Ordering
cmpList [] [] = EQ
cmpList [] _ = LT
cmpList _ [] = GT
cmpList (x:xs) (x':xs') = case cmp x x' of
    EQ -> cmpList xs xs'
    r  -> r

cmpIAOp :: IAOp -> IAOp -> Ordering
cmpIAOp ITimes _ = LT
cmpIAOp _ ITimes = GT
cmpIAOp IDiv _ = LT
cmpIAOp _ IDiv = GT
cmpIAOp IPower _ = LT
cmpIAOp _ IPower = GT
cmpIAOp IModOp _ = GT
cmpIAOp _ _ = error "<cmpIAOp>: not expected"

-- TODO: non-linear coeficients may need this as well
canonicalExpr :: IExpr -> IExpr
canonicalExpr (ISum l) = revert $ ISum $ combine $ sortBy cmp l
    where

    combine :: [IExpr] -> [IExpr]
    combine [] = []
    combine [i] = [i]
    combine (e1@(IArith ITimes (IInt n) (IIdx i)): e2@(IArith ITimes (IInt n') (IIdx i')) : xs) = let r = n + n' 
        in if i == i'
            then if r /= 0
                then combine (IArith ITimes (IInt r) (IIdx i) : xs)
                else combine xs
            else e1 : combine (e2 : xs)
    combine (x:xs) = x : combine xs

    revert :: IExpr -> IExpr
    revert (ISum [i@(IInt _)]) = i
    revert (ISum [IInt 0, IArith ITimes (IInt 1) v]) = v
    revert (ISum (IInt 0 : xs)) = ISum $ concatMap aux xs
    revert (ISum lst) = ISum $ concatMap aux lst
    revert lst = lst
    
    aux (IArith ITimes (IInt 1) e) = [e]
    aux (IArith ITimes (IInt 0) _) = []
    aux e = [e]
canonicalExpr e = e
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
-- C, 0 <= a |= 0 <= b  <==  |= a <= b'
    exactHyp (ILeq b) (ILeq a) = let
            (n,  c,  i) = decompose b
            (n', c', i') = decompose a 
        in if i == i' 
            then if evalBool [c .<. IInt 0, c' .<. IInt 0]
                then evalBool [(n .*. c') .<=. (n' .*. c)]
                else if evalBool [c .>. IInt 0, c' .>. IInt 0]
                    then evalBool [(n' .*. c) .<=. (n .*. c')]
                    else evalBool [a .<=. b]
            else evalBool [a .<=. b]

    exactHyp c (IAnd l) = checkHyp l c
    exactHyp _ _ = False

evalBool :: [ICond] -> Bool
evalBool = toBool . evalICond . IAnd
toBool :: ICond -> Bool
toBool (IBool b) = b
toBool _ = False 

-- (Term, Coeficient, Variable)
decompose :: IExpr -> (IExpr, IExpr, IExpr)
decompose (ISum [IInt n, IArith ITimes c i]) = (IInt n, c, i)
decompose (ISum [IInt n, i])                 = (IInt n, IInt 1, i)
decompose (ISum [IArith ITimes c i])         = (IInt 0, c, i)
decompose (IArith ITimes c i)                = (IInt 0, c, i)
decompose i                                  = (IInt 0, IInt 1, i)


iExpr2Expr :: (VarsIdTcM loc m,Location loc) => IExpr -> TcM loc m (Expression VarIdentifier Type)
iExpr2Expr = undefined
    
iCond2Expr :: (VarsIdTcM loc m,Location loc) => ICond -> TcM loc m (Expression VarIdentifier Type)
iCond2Expr = undefined



