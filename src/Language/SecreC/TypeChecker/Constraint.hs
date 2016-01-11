{-# LANGUAGE FlexibleInstances, ConstraintKinds, StandaloneDeriving, DeriveDataTypeable, MultiParamTypeClasses, TupleSections, GADTs, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Template
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.TypeChecker.Semantics
import Language.SecreC.TypeChecker.Index
import Language.SecreC.TypeChecker.SMT

import Control.Monad
import Control.Monad.Except
import qualified Control.Monad.State as State
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer
import Control.Monad.RWS as RWS

import Data.Bifunctor
import Data.Either
import Data.Monoid
import Data.Unique
import Data.Maybe
import Data.Foldable as Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Data hiding (cast)
import qualified Data.Map as Map
import Data.Generics hiding (LT,GT,cast)
import Data.List as List

import Text.PrettyPrint as PP hiding (equals)

-- * Constraint Engine

solveVarId :: (Vars (TcM loc) loc,Location loc) => loc -> VarIdentifier -> TcM loc ()
solveVarId l v = do
    cstrs <- liftM openedCstrs State.get
    deps <- liftIO $ varIdDeps v
    let deps' = Set.difference deps cstrs
    mapM_ (trySolveIOCstr l) deps'

-- | solves all constraints in the top environment
solve :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc ()
solve l doGuess = newErrorM $ do
--    ss <- ppConstraints =<< liftM (headNe . tDict) State.get
--    liftIO $ putStrLn $ "solve " ++ show doGuess ++ "[" ++ show ss ++ "\n]"
    solveCstrs l doGuess

-- solves all head constraints
solveCstrs :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc ()
solveCstrs l doGuess = do
--    ss <- ppConstraints =<< liftM (headNe . tDict) State.get
--    liftIO $ putStrLn $ "solveCstrs [" ++ show ss ++ "\n]"
--    doc <- liftM ppTSubsts getTSubsts
--    liftIO $ putStrLn $ show doc
    cstrs <- liftM (Map.elems . tCstrs . headNe . tDict) State.get
    let cs = filter (isTcCstr . kCstr . unLoc) cstrs
    go <- trySolveSomeCstrs doGuess cs
    case go of
        Left True -> solveCstrs l doGuess -- new substitions have been found, try again
        Left False -> when doGuess $ solveCheckCstrs -- run checks
        Right errs -> guessCstrs l doGuess errs -- nothing has progressed, try guessing

-- Left True = one constraint solved
-- Left False = no remaining unsolved constraints
-- Right err = failed
type SolveRes = Either Bool [(Unique,TCstr,SecrecError)]

solveGivenCstrs :: (VarsTcM loc,Location loc) => [Loc loc IOCstr] -> TcM loc ()
solveGivenCstrs = mapM_ (\(Loc l iok) -> solveIOCstr l iok)

solveCheckCstrs :: (VarsTcM loc,Location loc) => TcM loc ()
solveCheckCstrs = do
    ss <- ppConstraints =<< liftM (headNe . tDict) State.get
    liftIO $ putStrLn $ "solveCheckCstrs [" ++ show ss ++ "\n]"
    doc <- liftM ppTSubsts getTSubsts
    liftIO $ putStrLn $ show doc
    cstrs <- liftM (Map.elems . tCstrs . headNe . tDict) State.get
    let checks = filter (isCheckCstr . kCstr . unLoc) cstrs
    solveGivenCstrs checks

solveIOCstr :: (VarsTcM loc,Location loc) => loc -> IOCstr -> TcM loc ()
solveIOCstr l iok = resolveIOCstr l iok resolveTCstr

trySolveIOCstr :: (VarsTcM loc,Location loc) => loc -> IOCstr -> TcM loc ()
trySolveIOCstr l iok = solveIOCstr l iok `mplus` return ()

mergeSolveRes :: SolveRes -> SolveRes -> SolveRes
mergeSolveRes (Left True) b = Left True
mergeSolveRes (Left False) b = b
mergeSolveRes a (Left True) = Left True
mergeSolveRes a (Left False) = a
mergeSolveRes (Right a) (Right b) = Right (a ++ b)

-- | tries to solve one or more constraints
trySolveSomeCstrs :: (VarsTcM loc,Location loc) => Bool -> [Loc loc IOCstr] -> TcM loc SolveRes
trySolveSomeCstrs doAll = foldrM solveBound (Left False)
    where
    solveBound x@(Loc l iok) b = do
        ok <- trySolveCstr doAll x
        return (mergeSolveRes ok b)

getErrors :: [(Unique,TCstr,SecrecError)] -> [SecrecError]
getErrors = map thr3 . flattenErrors
    
flattenErrors :: [(Unique,TCstr,SecrecError)] -> [(Unique,TCstr,SecrecError)]
flattenErrors [] = []
flattenErrors ((x,y,MultipleErrors errs):xs) = flattenErrors (map (\e -> (x,y,e)) errs ++ xs)
flattenErrors (err:xs) = err : flattenErrors xs

getOpts :: Location loc => [(Unique,TCstr,SecrecError)] -> TcM loc (Maybe [TSubsts])
getOpts [] = return Nothing
getOpts ((u,x,y):xs) = case errorOpts x of
    Just opts -> do
        done <- isChoice u
        if done
            then getOpts xs
            else do
                addChoice u
                return $ Just opts
    otherwise -> getOpts xs

errorOpts :: TCstr -> Maybe [TSubsts]
errorOpts = everything append (mkQ Nothing aux)
    where
    aux :: TCstr -> Maybe [TSubsts]
    aux (TcK (MultipleSubstitutions v opts)) = Just $ map (Map.singleton v . fst) opts
    aux _ = Nothing
    append Nothing y = y
    append x y = x
    
filterErrors :: Location loc => Bool -> [(Unique,TCstr,SecrecError)] -> TcM loc [(Unique,TCstr,SecrecError)]
filterErrors False errs = do
    let errs1 = flattenErrors $ filter (not . isGlobalCstr . snd3) errs
    let errs2 = filter (not . isHaltError . thr3) errs1
    return errs2
filterErrors True errs = return errs

--filterWarnings :: Location loc => [(Unique,TCstr,SecrecError)] -> TcM loc [(Unique,TCstr,SecrecError)]
--filterWarnings = filterM $ \x -> if isOrWarnError (thr3 x)
--    then do
--        TcM $ lift $ tell [ErrWarn $ thr3 x]
--        return False
--    else return True

guessError :: Location loc => Bool -> [(Unique,TCstr,SecrecError)] -> TcM loc ()
guessError doAll errs = do
    errs' <- filterErrors doAll errs
--    ss <- ppConstraints =<< liftM (headNe . tDict) State.get
--    liftIO $ putStrLn $ "guessCstrs [" ++ show doAll ++ " " ++ show ss ++ "\n]"
--    liftIO $ putStrLn $ show $ and (map (\(_,k,e) -> isGlobalCstr k || isHaltError e) errs)
--    liftIO $ putStrLn $ show $ getErrors $ errs'
--    liftIO $ putStrLn "errs......."
    unless (null errs') $ throwError $ MultipleErrors $ getErrors errs'

guessCstrs :: (VarsTcM loc,Location loc) => loc -> Bool -> [(Unique,TCstr,SecrecError)] -> TcM loc ()
guessCstrs l False errs = guessError False errs
guessCstrs l True errs = do
    mb <- getOpts errs
    case mb of
        Nothing -> guessError True errs
        Just opts -> do
            tries <- steps opts
            unless (List.null tries) $ throwError $ TypecheckerError (locpos l) $ MultipleTypeSubstitutions tries
  where
    tryStep o e = text "Tried substitution:" <+> quotes (pp o) $+$ text "Sub-error:" <+> pp e
    steps [] = return []
    steps (o:os) = do
        tryO <- step o
        case tryO of
            Nothing -> return []
            Just err -> liftM (err:) (steps os)
    step o = (do
--        ss <- ppConstraints =<< liftM (headNe . tDict) State.get
--        liftIO $ putStrLn $ "guessStep [" ++ show ss ++ "\n]" ++ ppr o
        addSubstsM o
        solveCstrs l True
        return Nothing) `catchError` \e -> return (Just $ tryStep o e)

trySolveCstr :: (VarsTcM loc,Location loc) => Bool -> Loc loc IOCstr -> TcM loc SolveRes
trySolveCstr False (Loc l iok) | isGlobalCstr (kCstr iok) = do
    return $ Right [(uniqId $ kStatus iok,kCstr iok,GenericError (locpos l) $ text "Unsolved global constraint")]
trySolveCstr doAll (Loc l iok) = do
    (resolveIOCstr l iok resolveTCstr >> return (Left True)) `catchError` processError
  where
    processError e = return $ Right [(uniqId $ kStatus iok,kCstr iok,e)]

-- * Throwing Constraints

-- throws a constraint

checkCstrM :: Location loc => loc -> CheckCstr -> TcM loc ()
checkCstrM l k = do
    hyps <- tcPos getHyps
    tCstrM l $ CheckK hyps k

tCstrM :: Location loc => loc -> TCstr -> TcM loc ()
tCstrM l k = do
    err <- askErrorM
    let k' = DelayedK k err
    newTemplateConstraint l k'
    return ()

tcCstrM :: Location loc => loc -> TcCstr -> TcM loc ()
tcCstrM l k = tCstrM l $ TcK k

tcTopCstrM :: Location loc => loc -> TcCstr -> TcM loc ()
tcTopCstrM l k = newErrorM $ addErrorM (topCstrErr (locpos l) $ TcK k) $ tcCstrM l k

-- | error-handling for a top-level delayed constraint
topCstrErr :: Position -> TCstr -> SecrecError -> SecrecError
topCstrErr p (TcK (Unifies t1 t2)) err = TypecheckerError p $ UnificationException (pp t1) (pp t2) $ Right err
topCstrErr p (TcK (Coerces e1 t1 e2 t2)) err = TypecheckerError p $ CoercionException (pp t1) (pp t2) $ Right err
topCstrErr p (TcK (Coerces2 e1 t1 e2 t2 v1 v2 x)) err = TypecheckerError p $ BiCoercionException (Just $ pp x) (pp t1) (pp t2) $ Right err
topCstrErr p (TcK (Equals t1 t2)) err = TypecheckerError p $ EqualityException (pp t1) (pp t2) $ Right err
topCstrErr p (TcK (CoercesSec e1 t1 e2 t2)) err = TypecheckerError p $ CoercionException (pp t1) (pp t2) $ Right err
topCstrErr p (TcK (Coerces2Sec e1 t1 e2 t2 v1 v2 x)) err = TypecheckerError p $ BiCoercionException (Just $ pp x) (pp t1) (pp t2) $ Right err
topCstrErr p (TcK (PDec {})) err = err
topCstrErr p (TcK (TRet {})) err = err
topCstrErr p (TcK (TDec {})) err = err
topCstrErr p t err = err

resolveTCstr :: (VarsTcM loc,Location loc) => loc -> TCstr -> TcM loc ()
resolveTCstr l k@(TcK (TRet t x)) = do
    res <- templateDecReturn l t
    addErrorM
        (TypecheckerError (locpos l) . TemplateSolvingError (text "Return type of" <+> quotes (pp t)))
        (tcCstrM l $ Unifies res x)
resolveTCstr l k@(TcK (TDec n args x)) = do
    (res,Nothing) <- matchTemplate l True (Left n) (Just args) Nothing Nothing (checkTemplateType $ fmap (const l) n)
    addErrorM
        (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp n <+> parens (sepBy comma $ map pp args))))
        (tcCstrM l $ Unifies (DecT res) (DecT x))
resolveTCstr l k@(TcK (PDec (Left n) specs args r x xs)) = do
    let doCoerce = isJust xs
    (res,Just rs) <- matchTemplate l doCoerce (Right $ Left n) specs (Just args) (Just r) (checkProcedure $ fmap (const l) n)
    addErrorM (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp r <+> pp n <+> parens (sepBy comma $ map pp args)))) $ do
        tcCstrM l $ Unifies (DecT res) (DecT x)
        when doCoerce $ unifiesList l (map varIdxT rs) (map varIdxT $ fromJust xs)
resolveTCstr l k@(TcK (PDec (Right o) specs args r x xs)) = do
    let doCoerce = isJust xs
    (res,Just rs) <- matchTemplate l doCoerce (Right $ Right o) specs (Just args) (Just r) (checkOperator $ fmap (const l) o)
    addErrorM (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp r <+> pp o <+> parens (sepBy comma $ map pp args)))) $ do
        tcCstrM l $ Unifies (DecT res) (DecT x)
        when doCoerce $ unifiesList l (map varIdxT rs) (map varIdxT $ fromJust xs)
resolveTCstr l k@(TcK (Equals t1 t2)) = do
    equals l t1 t2
resolveTCstr l k@(TcK (Coerces e1 t1 x2 t2)) = do
    coerces l e1 t1 x2 t2
--resolveTCstr l k@(Coerces2 t1 t2 x) = do
--    res <- coerces2 l t1 t2
--    addErrorM
--        (TypecheckerError (locpos l) . BiCoercionException (Just $ pp x) (pp t1) (pp t2) . Right)
--        (tcCstrM l $ Unifies res x)
resolveTCstr l k@(TcK (CoercesSec e1 t1 x2 t2)) = do
    coercesSec l e1 t1 x2 t2
--resolveTCstr l k@(Coerces2Sec t1 t2 b x) = do
--    s3 <- coerces2Sec l t1 t2 b
--    addErrorM
--        (TypecheckerError (locpos l) . BiCoercionException (Just $ pp x) (pp t1) (pp t2) . Right)
--        (tcCstrM l $ Unifies (SecT s3) (SecT x))
resolveTCstr l k@(TcK (Unifies t1 t2)) = do
    unifies l t1 t2
resolveTCstr l k@(TcK (SupportedPrint t xs)) = do
    isSupportedPrint l t xs
resolveTCstr l k@(TcK (ProjectStruct t a x)) = do
    addErrorM
        (TypecheckerError (locpos l) . UnresolvedFieldProjection (pp t) (pp a <+> char '=' <+> pp x))
        (projectStructField l t a >>= \res -> tcCstrM l $ Unifies res x)
resolveTCstr l k@(TcK (ProjectMatrix ct rngs x)) = do
    addErrorM
        (TypecheckerError (locpos l) . UnresolvedMatrixProjection (pp ct) (brackets (ppArrayRanges rngs) <+> char '=' <+> pp x))
        (projectMatrixType l ct rngs >>= \res -> tcCstrM l $ Unifies (ComplexT res) (ComplexT x))
resolveTCstr l k@(TcK (IsReturnStmt cs ret dec)) = do
    isReturnStmt l cs ret dec
resolveTCstr l (DelayedK k err) = do
    addErrorM err $ resolveTCstr l k
resolveTCstr l (TcK (MultipleSubstitutions v s)) = do
    multipleSubstitutions l v s
resolveTCstr l (TcK (MatchTypeDimension t d)) = matchTypeDimension l t d
resolveTCstr l (HypK h) = do
    resolveHypCstr l h
    return ()
resolveTCstr l (CheckK hyps c) = do
    withHypotheses GlobalScope $ do
        tcPos $ State.modify $ \env -> env { globalHyps = Set.empty, localHyps = hyps }
        resolveCheckCstr l c

resolveHypCstr :: (VarsTcM loc,Location loc) => loc -> HypCstr -> TcM loc (Maybe (ICond VarIdentifier))
resolveHypCstr l hyp = newErrorM $ addErrorM (TypecheckerError (locpos l) . FailAddHypothesis (pp hyp)) $ orWarn $ resolveHypCstr' hyp
    where
    resolveHypCstr' (HypCondition c) = expr2ICond $ fmap (Typed l) c
    resolveHypCstr' (HypNotCondition c) = liftM INot $ expr2ICond $ fmap (Typed l) c
    resolveHypCstr' (HypAssign (VarName t n) e) = do
        i <- expr2IExprAs (fmap (Typed l) e) t
        return $ IIdx n .==. i
    resolveHypCstr' (HypEqual e1 e2) = do
        i1 <- expr2IExpr $ fmap (Typed l) e1
        i2 <- expr2IExpr $ fmap (Typed l) e2
        return $ i1 .==. i2
    
resolveCheckCstr :: (VarsTcM loc,Location loc) => loc -> CheckCstr -> TcM loc ()
resolveCheckCstr l (CheckAssertion c) = checkAssertion l c
resolveCheckCstr l (CheckIndex e) = checkIndex l e
resolveCheckCstr l (CheckArrayAccess t d low up sz) = checkArrayAccess l t d low up sz
resolveCheckCstr l (IsValid c) = isValid l c

solveHypotheses :: (Vars (TcM loc) loc,Location loc) => TcM loc [ICond VarIdentifier]
solveHypotheses = do
    hyps <- liftM Set.toList getHyps
    liftM concat $ mapM (\(Loc l iok) -> liftM maybeToList $ resolveIOCstr l iok (\l (HypK k) -> resolveHypCstr l k)) hyps

tcProve :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc (a,TDict loc)
tcProve l doGuess m = do
    newDict l
    x <- m
    solve l doGuess
    d <- liftM (headNe . tDict) State.get
    State.modify $ \e -> e { tDict = updDict (tDict e) }
    return (x,d)
  where
    updDict (ConsNe x xs) = xs

proveWith :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc (Either SecrecError (a,TDict loc))
proveWith l doGuess proof = try `catchError` (return . Left)
    where
    try = liftM Right $ tcProve l doGuess proof

prove :: (VarsTcM loc,Location loc) => loc -> Bool -> TcM loc a -> TcM loc a
prove l doGuess m = do
    (a,dict) <- tcProve l doGuess m
    addHeadTDict dict
    return a

-- * Solving constraints

multipleSubstitutions :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> [(Type,[TcCstr])] -> TcM loc ()
multipleSubstitutions l v ss = do
    t <- resolveTVar l v
    ok <- matchOne l t ss
    case ok of
        Nothing -> return ()
        Just errs -> tcError (locpos l) $ MultipleTypeSubstitutions errs

matchOne :: (VarsTcM loc,Location loc) => loc -> Type -> [(Type,[TcCstr])] -> TcM loc (Maybe [Doc])
matchOne l t1 [] = return $ Just []
matchOne l t1 ((t,ks):ts) = do
    ok <- tryUnifies l t1 t
    case ok of
        Nothing -> do
            mapM_ (tcCstrM l) ks
            liftM conc $ mapM (\t -> tryNotUnifies l t1 t) $ map fst ts
        Just err -> liftM (fmap (pp err:)) $ matchOne l t1 ts
 where
    conc [] = Nothing
    conc (Left x:xs) = fmap (x:) (conc xs)
    conc (Right x:xs) = fmap (pp x:) (conc xs)
        
tryUnifies :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc (Maybe SecrecError)
tryUnifies l t1 t2 = (unifies l t1 t2 >> return Nothing) `catchError` (return . Just)

tryNotUnifies :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc (Either Doc SecrecError)
tryNotUnifies l t1 t2 = (prove l True (unifies l t1 t2) >> return (Right err)) `catchError` handleErr
    where
    err = GenericError (locpos l) $ text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "should not unify."
    ok = text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "unify."
    handleErr e = if isHaltError e
        then throwError e
        else return $ Left ok

-- checks if two types are equal, without using coercions, not performing substitutions
equals :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc ()
equals l (NoType _) (NoType _) = return ()
equals l (IdxT e1) (IdxT e2) = do
    equalsExpr l e1 e2
equals l (SysT t1) (SysT t2) = do
    equalsSys l t1 t2
equals l (DecT d1) (DecT d2) = do
    equalsDec l d1 d2
equals l (SecT s1) (SecT s2) = do
    equalsSec l s1 s2
equals l (BaseT b1) (BaseT b2) = do
    equalsBase l b1 b2
equals l (ComplexT c1) (ComplexT c2) = do
    equalsComplex l c1 c2
equals l (ComplexT c1) (BaseT b2) = do
    equalsComplex l c1 (defCType b2)
equals l (BaseT b1) (ComplexT c2) = do
    equalsComplex l (defCType b1) c2
equals l TType TType = return ()
equals l DType DType = return ()
equals l BType BType = return ()
equals l KType KType = return ()
equals l (SType k1) (SType k2) | k1 == k2 = return ()
equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
equals l (CondType t1 c1) (CondType t2 c2) = do
    equals l t1 t2
    equalsSCond l c1 c2
equals l t1 t2 = constraintError EqualityException l t1 t2 Nothing

equalsSys :: (VarsTcM loc,Location loc) => loc -> SysType -> SysType -> TcM loc ()
equalsSys l (SysPush t1) (SysPush t2) = tcCstrM l $ Equals t1 t2
equalsSys l (SysRet t1) (SysRet t2) = tcCstrM l $ Equals t1 t2
equalsSys l (SysRef t1) (SysRef t2) = tcCstrM l $ Equals t1 t2
equalsSys l (SysCRef t1) (SysCRef t2) = tcCstrM l $ Equals t1 t2
equalsSys l t1 t2 = constraintError EqualityException l t1 t2 Nothing

equalsSec :: (VarsTcM loc,Location loc) => loc -> SecType -> SecType -> TcM loc ()
equalsSec l Public Public = return ()
equalsSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
equalsSec l (SVar v1 k1) (SVar v2 k2) | v1 == v2 && k1 == k2 = return ()
equalsSec l (SVar v _) s2 = do
    s1 <- resolveSVar l v
    tcCstrM l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 (SVar v _) = do
    s2 <- resolveSVar l v
    tcCstrM l $ Equals (SecT s1) (SecT s2)

equalsDec :: (VarsTcM loc,Location loc) => loc -> DecType -> DecType -> TcM loc ()
equalsDec l (DVar v1) (DVar v2) | v1 == v2 = return ()
equalsDec l (DVar v1) d2 = do
    d1 <- resolveDVar l v1
    tcCstrM l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 (DVar v2) = do
    d2 <- resolveDVar l v2
    tcCstrM l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 d2 | decTypeTyVarId d1 == decTypeTyVarId d2 = return ()
equalsDec l d1 d2 = constraintError EqualityException l d1 d2 Nothing

equalsComplex :: (VarsTcM loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc ()
equalsComplex l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
equalsComplex l (ArrayLit es1) (ArrayLit es2) | length es1 == length es2 = do
    mapM_ (\(x,y) -> tcCstrM l $ Equals (IdxT x) (IdxT y)) $ zip (Foldable.toList es1) (Foldable.toList es2)
equalsComplex l (CType s1 t1 d1 sz1) (CType s2 t2 d2 sz2) = do
    tcCstrM l $ Equals (SecT s1) (SecT s2)
    tcCstrM l $ Equals (BaseT t1) (BaseT t2)
    tcCstrM l $ Equals (IdxT d1) (IdxT d2)
    mapM_ (\(x,y) -> tcCstrM l $ Equals (IdxT x) (IdxT y)) =<< zipSizes l sz1 sz2
equalsComplex l (CVar v1) (CVar v2) | v1 == v2 = return ()
equalsComplex l (CVar v) c2 = do
    c1 <- resolveCVar l v
    tcCstrM l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l c1 (CVar v) = do
    c2 <- resolveCVar l v
    tcCstrM l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l Void Void = return ()
equalsComplex l c1 c2 = constraintError EqualityException l c1 c2 Nothing

equalsBase :: (VarsTcM loc,Location loc) => loc -> BaseType -> BaseType -> TcM loc ()
equalsBase l (BVar v1) (BVar v2) | v1 == v2 = return ()
equalsBase l (BVar v) t2 = do
    t1 <- resolveBVar l v
    tcCstrM l $ Equals (BaseT t1) (BaseT t2)
equalsBase l t1 (BVar v) = do
    t2 <- resolveBVar l v
    tcCstrM l $ Equals (BaseT t1) (BaseT t2)
equalsBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2
equalsBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
equalsBase l b1 b2 = constraintError EqualityException l b1 b2 Nothing

equalsFoldable :: (VarsTcM loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc ()
equalsFoldable l xs ys = equalsList l (toList xs) (toList ys)

equalsList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
equalsList l [] [] = return ()
equalsList l (x:xs) (y:ys) = do
    tcCstrM l $ Equals x y
    equalsList l xs ys
equalsList l xs ys = constraintError EqualityException l xs ys Nothing

zipSizes :: (VarsTcM loc,Location loc) => loc -> [Expression VarIdentifier Type] -> [Expression VarIdentifier Type] -> TcM loc [(Expression VarIdentifier Type,Expression VarIdentifier Type)]
zipSizes l [] [] = return []
zipSizes l [] (y:ys) = do
    x <- newSizeVar
    zs <- zipSizes l [] ys
    return ((x,y):zs)
zipSizes l (x:xs) [] = do
    y <- newSizeVar
    zs <- zipSizes l xs []
    return ((x,y):zs)
zipSizes l (x:xs) (y:ys) = do
    rs <- zipSizes l xs ys
    return ((x,y):rs)

equalsPrim :: Location loc => loc -> PrimitiveDatatype () -> PrimitiveDatatype () -> TcM loc ()
equalsPrim l p1 p2 | p1 == p2 = return ()
equalsPrim l t1 t2 = constraintError EqualityException l t1 t2 Nothing

equalsExpr :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()
equalsExpr l e1 e2 | funit e1 == funit e2 = return ()
equalsExpr l e1 e2 = do
    v1 <- addErrorM
        (TypecheckerError (locpos l) . EqualityException (pp e1) (pp e2) . Right)
        (evaluateExpr $ fmap (Typed l) e1)
    v2 <- addErrorM
        (TypecheckerError (locpos l) . EqualityException (pp e1) (pp e2) . Right)
        (evaluateExpr $ fmap (Typed l) e2)
    let ce1' = funit e1
    let ce2' = funit e2
    unless (v1 == v2) $ constraintError EqualityException l (ce1') (ce2') Nothing

expandCTypeVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc ComplexType
expandCTypeVar l v = do
    d <- newDomainTyVar AnyKind
    t <- newBaseTyVar
    dim <- newDimVar
    let ct = CType d t dim []
    addSubstM l (fmap (const TType) v) $ ComplexT ct
    return ct

-- | Non-directed coercion, with implicit security coercions.
-- Returns the unified type.
-- applies substitutions
--coerces2 :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc Type
--coerces2 l (BaseT t1) (BaseT t2) = do
--    unifiesBase l t1 t2
--    return (BaseT t1)
--coerces2 l (ComplexT t1) (ComplexT t2) = liftM ComplexT $ coerces2Complex l t1 t2
--coerces2 l (ComplexT c1) (BaseT b2) = liftM ComplexT $ coerces2Complex l c1 (defCType b2)
--coerces2 l (BaseT b1) (ComplexT c2) = liftM ComplexT $ coerces2Complex l (defCType b1) c2
--coerces2 l (IdxT e1) (IdxT e2) = do
--    unifiesExpr l e1 e2
--    return (IdxT e1)
--coerces2 l (SecT s1) (SecT s2) = liftM SecT $ coerces2Sec l s1 s2 (defCType index)
--coerces2 l (SysT s1) (SysT s2) = liftM SysT $ coerces2Sys l s1 s2
--coerces2 l (CondType t1 c1) (CondType t2 c2) = do
--    t3 <- coerces2 l t1 t2
--    c3 <- landExprs l c1 c2
--    return $ CondType t3 c3
--coerces2 l (CondType t1 c1) t2 = do
--    t3 <- coerces2 l t1 t2
--    return $ CondType t3 c1
--coerces2 l t1 (CondType t2 c2) = do
--    t3 <- coerces2 l t1 t2
--    return $ CondType t3 c2
--coerces2 l t1 t2 = addErrorM
--    (TypecheckerError (locpos l) . BiCoercionException Nothing (pp t1) (pp t2) . Right)
--    (equals l t1 t2 >> return t1)
--
--coerces2Complex :: (VarsTcM loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc ComplexType
--coerces2Complex l t1 t2 | isVoid t1 || isVoid t2 = addErrorM
--    (TypecheckerError (locpos l) . BiCoercionException Nothing (pp t1) (pp t2) . Right)
--    (unifiesComplex l t1 t2 >> return t1)
--coerces2Complex l t1@(isLitCType -> True) t2@(isLitCType -> True) = do
--    v@(ComplexT c) <- newTyVar
--    tcCstrM l $ Coerces (ComplexT t1) v
--    tcCstrM l $ Coerces (ComplexT t2) v
--    return c
--coerces2Complex l (TyLit lit) t2 = do
--    coercesLitComplex l lit t2 -- literals are never variables
--    return t2
--coerces2Complex l (ArrayLit lit) t2 = do
--    coercesArrayLitComplex l lit t2 -- literals are never variables
--    return t2
--coerces2Complex l t1 (TyLit lit) = do
--    coercesLitComplex l lit t1 -- literals are never variables
--    return t1
--coerces2Complex l t1 (ArrayLit lit) = do
--    coercesArrayLitComplex l lit t1 -- literals are never variables
--    return t1
--coerces2Complex l (CType s1 t1 d1 sz1) ct2@(CType s2 t2 d2 sz2) = do
--    tcCstrM l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
--    tcCstrM l $ Unifies (IdxT d1) (IdxT d2)
--    unifiesSizes l d1 sz1 d2 sz2
--    s3 <- newDomainTyVar AnyKind
--    tcCstrM l $ Coerces2Sec s1 s2 ct2 s3
--    return $ CType s3 t1 d1 sz1
--coerces2Complex l t1@(CVar v1) t2@(CVar v2) = do
--    mb1 <- tryResolveCVar l v1
--    mb2 <- tryResolveCVar l v2
--    t3 <- newTyVar
--    case (mb1,mb2) of
--        (Just t1',Just t2') -> tcCstrM l $ Coerces2 (ComplexT t1') (ComplexT t2') t3
--        (Just t1',Nothing) -> tcCstrM l $ Coerces2 (ComplexT t1') (ComplexT t2) t3
--        (Nothing,Just t2') -> tcCstrM l $ Coerces2 (ComplexT t1) (ComplexT t2') t3
--        (Nothing,Nothing) -> constraintError (BiCoercionException Nothing) l t1 t2 Nothing
--    typeToComplexType l t3
--coerces2Complex l t1@(CVar v) t2 = do
--    mb <- tryResolveCVar l v
--    t3 <- newTyVar
--    case mb of
--        Just t1' -> do
--            tcCstrM l $ Coerces2 (ComplexT t1') (ComplexT t2) t3
--        Nothing -> do
--            t1' <- expandCTypeVar l v
--            tcCstrM l $ Coerces2 (ComplexT t1') (ComplexT t2) t3
--    typeToComplexType l t3
--coerces2Complex l t1 t2@(CVar v) = do
--    mb <- tryResolveCVar l v
--    t3 <- newTyVar
--    case mb of
--        Just t2' -> do
--            tcCstrM l $ Coerces2 (ComplexT t1) (ComplexT t2') t3
--        Nothing -> do
--            t2' <- expandCTypeVar l v
--            tcCstrM l $ Coerces2 (ComplexT t1) (ComplexT t2') t3
--    typeToComplexType l t3
--coerces2Complex l c1 c2 = constraintError (BiCoercionException Nothing) l c1 c2 Nothing
--
--coerces2Sec :: (VarsTcM loc,Location loc) => loc -> SecType -> SecType -> ComplexType -> TcM loc SecType
--coerces2Sec l s1 s2 ct = do
--    opts <- TcM $ lift Reader.ask
--    if implicitClassify opts
--        then addErrorM
--                (TypecheckerError (locpos l) . BiCoercionException Nothing (pp s1) (pp s2) . Right)
--                ((prove l False (coercesSec l s1 s2 ct >> return s2)) `mplus` (prove l False (coercesSec l s2 s1 ct >> return s1)))
--        else unifiesSec l s1 s2 >> return s1

--coerces2Sys :: (VarsTcM loc,Location loc) => loc -> SysType -> SysType -> TcM loc SysType
--coerces2Sys l (SysPush t1) (SysPush t2) = do
--    t3 <- newTyVar
--    tcCstrM l $ Coerces2 t1 t2 t3
--    return $ SysPush t3
--coerces2Sys l (SysRet t1) (SysRet t2) = do
--    t3 <- newTyVar
--    tcCstrM l $ Coerces2 t1 t2 t3
--    return $ SysRet t3
--coerces2Sys l (SysRef t1) (SysRef t2) = do
--    t3 <- newTyVar
--    tcCstrM l $ Coerces2 t1 t2 t3
--    return $ SysRef t3
--coerces2Sys l (SysCRef t1) (SysCRef t2) = do
--    t3 <- newTyVar
--    tcCstrM l $ Coerces2 t1 t2 t3
--    return $ SysCRef t3
--coerces2Sys l t1 t2 = constraintError (BiCoercionException Nothing) l t1 t2 Nothing

coercesE :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Type -> Type -> TcM loc (Expression VarIdentifier Type)
coercesE l e1 t1 t2 = do
    x2 <- newTypedVar t2
    coerces l e1 t1 x2 t2
    return $ varExpr x2

-- | Directed coercion, with implicit security type coercions and literal coercions
-- applies substitutions
-- returns a classify declaration
coerces :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Type -> VarName VarIdentifier Type -> Type -> TcM loc ()
coerces l e1 (BaseT b1) x2 t2@(BaseT b2) = do
    unifiesBase l b1 b2
    unifiesExpr l (varExpr x2) e1
coerces l e1 t1@(ComplexT ct1) x2 t2@(ComplexT ct2) = do
    coercesComplex l e1 ct1 x2 ct2
    unifiesExpr l (varExpr x2) e1
coerces l e1 t1@(ComplexT c1) x2 t2@(BaseT b2) = do
    coercesComplex l e1 c1 x2 (defCType b2)
    unifiesExpr l (varExpr x2) e1
coerces l e1 t1@(BaseT b1) x2 t2@(ComplexT c2) = do
    coercesComplex l e1 (defCType b1) x2 c2
    unifiesExpr l (varExpr x2) e1
--coerces l (IdxT e1) (IdxT e2) = unifiesExpr l e1 e2
--coerces l (SecT s1) (SecT s2) = coercesSec l s1 s2 (defCType index)
--coerces l e1 (SysT s1) (SysT s2) = coercesSys l e1 s1 s2
--coerces l t1@(CondType t1' c1) t2 = do
--    coerces l t1' t2
--    satisfiesSConds l [c1]
--coerces l t1 t2@(CondType t2' c2) = do
--    coerces l t1 t2'
--    satisfiesSConds l [c2]
coerces l e1 t1 x2 t2 = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp t1) (pp t2) . Right)
    (unifies l t1 t2 >> unifiesExpr l (varExpr x2) e1)

--coercesSys :: (VarsTcM loc,Location loc) => loc -> SyscallParameter VarIdentifier Type -> SysType -> SysType -> TcM loc (SyscallParameter VarIdentifier Type)
--coercesSys l (SyscallPush _ e1) (SysPush t1) s2@(SysPush t2) = do
--    v2 <- newTypedVar t2
--    tcCstrM l $ Coerces e1 t1 (funit v2) t2
--    return $ SyscallPush (SysT s2) $ RVariablePExpr (SysT s2) v2  
--coercesSys l e1 (SysRet t1) (SysRet t2) = tcCstrM l $ Coerces t1 t2
--coercesSys l e1 (SysRef t1) (SysRef t2) = tcCstrM l $ Coerces t1 t2
--coercesSys l e1 (SysCRef t1) (SysCRef t2) = tcCstrM l $ Coerces t1 t2
--coercesSys l e1 t1 t2 = constraintError CoercionException l t1 t2 Nothing

coercesComplexE :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> ComplexType -> ComplexType -> TcM loc (Expression VarIdentifier Type)
coercesComplexE l e1 ct1 ct2 = do
    x2 <- newTypedVar $ ComplexT ct2
    coercesComplex l e1 ct1 x2 ct2
    return $ varExpr x2

coercesComplex :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> ComplexType -> VarName VarIdentifier Type -> ComplexType -> TcM loc ()
coercesComplex l e1 t1 x2 t2 | isVoid t1 || isVoid t2 = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp t1) (pp t2) . Right)
    (unifiesComplex l t1 t2 >> addValue l (fmap (const $ ComplexT t2) x2) e1)
coercesComplex l e1 (TyLit lit) x2 t2 = do
    e2 <- coercesLitComplex l e1 lit t2 -- literals are never variables
    unifiesExpr l (varExpr x2) e2
coercesComplex l e1 (ArrayLit lit) x2 t2 = do
    e2 <- coercesArrayLitComplex l e1 lit t2 -- literals are never variables
    unifiesExpr l (varExpr x2) e2
coercesComplex l e1 ct1@(CType s1 t1 d1 sz1) x2 ct2@(CType s2 t2 d2 sz2) = do
    tcCstrM l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
    tcCstrM l $ Unifies (IdxT d1) (IdxT d2)
    unifiesSizes l d1 sz1 d2 sz2
    tcCstrM l $ CoercesSec e1 ct1 x2 s2
coercesComplex l e1 ct1@(CVar v1) x2 ct2@(CVar v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just ct1',Just ct2') -> do
            tcCstrM l $ Coerces e1 (ComplexT ct1') x2 (ComplexT ct2')
        (Just ct1',Nothing) -> do
            tcCstrM l $ Coerces e1 (ComplexT ct1') x2 (ComplexT ct2)
        (Nothing,Just ct2') -> do
            tcCstrM l $ Coerces e1 (ComplexT ct1) x2 (ComplexT ct2')
        (Nothing,Nothing) -> constraintError CoercionException l ct1 ct2 Nothing
coercesComplex l e1 (CVar v) x2 ct2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct1' -> coercesComplex l e1 ct1' x2 ct2
        Nothing -> do
            ct1' <- expandCTypeVar l v
            tcCstrM l $ Coerces e1 (ComplexT ct1') x2 (ComplexT ct2)
coercesComplex l e1 ct1 x2 (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct2' -> coercesComplex l e1 ct1 x2 ct2'
        Nothing -> do
            ct2' <- expandCTypeVar l v
            tcCstrM l $ Coerces e1 (ComplexT ct1) x2 (ComplexT ct2')
coercesComplex l e1 c1 x2 c2 = constraintError CoercionException l c1 c2 Nothing

cSec (CType s _ _ _) = s

coercesSecE :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> ComplexType -> SecType -> TcM loc (Expression VarIdentifier Type)
coercesSecE l e1 ct1 s2 = do
    let t2 = ComplexT $ setCSec ct1 s2
    x2 <- newTypedVar t2
    coercesSec l e1 ct1 x2 s2
    return $ varExpr x2

coercesSec :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> ComplexType -> VarName VarIdentifier Type -> SecType -> TcM loc ()
coercesSec l e1 ct1 x2 s2 = do
    opts <- TcM $ lift Reader.ask
    if implicitClassify opts
        then coercesSec' l e1 ct1 x2 s2
        else do
            let t2 = ComplexT $ setCSec ct1 s2
            unifiesSec l (cSec ct1) s2
            unifiesExpr l (varExpr x2) e1

coercesSec' :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> ComplexType -> VarName VarIdentifier Type -> SecType -> TcM loc ()
coercesSec' l e1 (cSec -> SVar v1 k1) x2 (SVar v2 k2) | v1 == v2 && k1 == k2 = unifiesExpr l (varExpr x2) e1
coercesSec' l e1 (cSec -> Public) x2 Public = unifiesExpr l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Public) x2 s2@(SVar v AnyKind) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2 -> tcCstrM l $ CoercesSec e1 ct1 x2 s2
        Nothing -> do
            v' <- newDomainTyVar $ PrivateKind Nothing
            let ex2 = varExpr x2
            tcCstrM l $ MultipleSubstitutions v [(SecT Public,[Unifies (IdxT ex2) (IdxT e1)]),(SecT v',[CoercesSec e1 ct1 x2 v'])]
coercesSec' l e1 ct1@(cSec -> Public) x2 s2@(SVar v k) = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp ct1) (pp s2) . Right)
    (do
        s2' <- resolveSVar l v
        tcCstrM l $ CoercesSec e1 ct1 x2 s2'
    )
coercesSec' l e1 ct1@(cSec -> s1@(SVar v _)) x2 s2@(Public) = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp ct1) (pp s2) . Right)
    (do
        tcCstrM l $ Unifies (SecT s1) (SecT s2)
        unifiesExpr l (varExpr x2) e1
    )
coercesSec' l e1 ct1@(cSec -> Private d1 k1) x2 (Private d2 k2) | d1 == d2 && k1 == k2 = unifiesExpr l (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> s1@(Private d1 k1)) x2 s2@(SVar v _) = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp ct1) (pp s2) . Right)
    (do
        tcCstrM l $ Unifies (SecT s1) (SecT s2)
        unifiesExpr l (varExpr x2) e1
    )
--coercesSec' l e1 ct1@(cSec -> SVar v AnyKind) x2 s2@(Private d2 k2) = do
--    mb <- tryResolveSVar l v
--    case mb of
--        Just s1 -> tcCstrM l $ CoercesSec e1 s1 x2 s2
--        Nothing -> do
--            tcCstrM l $ MultipleSubstitutions v [(SecT Public,[]),(SecT s2,[])]
coercesSec' l e1 ct1@(cSec -> s1@(SVar v _)) x2 s2@(Private d2 k2) = addErrorM
    (TypecheckerError (locpos l) . CoercionException (pp ct1) (pp s2) . Right)
    (do
        tcCstrM l $ Unifies (SecT s1) (SecT s2)
        unifiesExpr l (varExpr x2) e1
    )
coercesSec' l e1 ct1@(cSec -> Public) x2 s2@(Private d2 k2) = do
    let ct2 = setCSec ct1 s2
    let classify = ProcedureName () $ mkVarId "classify"
    (dec,_) <- tcTopPDecCstrM l False (Left classify) Nothing [e1] (ComplexT ct2)
    unifiesExpr l (varExpr x2) $ ProcCallExpr (ComplexT ct2) (fmap (const $ DecT dec) classify) Nothing [e1]
coercesSec' l e1 ct1@(cSec -> SVar v1 _) x2 s2@(SVar v2 _) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just t1',Just t2') -> tcCstrM l $ CoercesSec e1 (setCSec ct1 t1') x2 t2'
        (Just t1',Nothing) -> tcCstrM l $ CoercesSec e1 (setCSec ct1 t1') x2 s2
        (Nothing,Just t2') -> tcCstrM l $ CoercesSec e1 ct1 x2 t2'
        (Nothing,Nothing) -> constraintError (\x y -> Halt . CoercionException x y) l ct1 s2 Nothing
coercesSec' l e1 t1 x2 t2 = constraintError CoercionException l t1 t2 Nothing

-- | coerces a literal into a primitive type
coercesLitComplex :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Literal () -> ComplexType -> TcM loc (Expression VarIdentifier Type)
coercesLitComplex l e1 lit ct@(CType s t d sz) = do
    coercesLitBase l lit t
    x <- newTypedVar $ ComplexT ct
    tcCstrM l $ CoercesSec e1 (defCType t) x s  -- coerce the security type
    return $ varExpr x
coercesLitComplex l e1 lit (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> coercesLitComplex l e1 lit c2
        Nothing -> do
            c2 <- expandCTypeVar l v
            coercesLitComplex l e1 lit c2
coercesLitComplex l e1 l1@(IntLit _ i1) ct2@(TyLit (IntLit _ i2)) | i1 == i2 = do
    let t2 = ComplexT ct2
    return $ fmap (const t2) e1
coercesLitComplex l e1 l1@(FloatLit _ f1) ct2@(TyLit (FloatLit _ f2)) | f1 == f2 = do
    let t2 = ComplexT ct2
    return $ fmap (const t2) e1
coercesLitComplex l e1 l1@(IntLit _ i1) ct2@(TyLit (FloatLit _ f2)) | fromInteger i1 == f2 = do
    let t2 = ComplexT ct2
    return $ fmap (const t2) e1
coercesLitComplex l e1 l1@(FloatLit _ f1) ct2@(TyLit (IntLit _ i2)) | f1 == fromInteger i2 = do
    let t2 = ComplexT ct2
    return $ fmap (const t2) e1
coercesLitComplex l e1 l1 ct2@(TyLit l2) | l1 == l2 = do
    let t2 = ComplexT ct2
    return $ fmap (const t2) e1
coercesLitComplex l e1 l1 t2 = constraintError CoercionException l l1 t2 Nothing  
    
coercesArrayLitComplex :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> NeList (Expression VarIdentifier Type) -> ComplexType -> TcM loc (Expression VarIdentifier Type)
coercesArrayLitComplex l e1 es ct@(CType s t d sz) = do -- TODO: check size of fixed array?
    mapM_ (\e -> tcCstrM l $ Unifies (loc e) $ BaseT t) es
    x <- newTypedVar $ ComplexT ct
    tcCstrM l $ CoercesSec e1 (defCType t) x s -- coerce the security type
    return $ varExpr x
coercesArrayLitComplex l e1 es (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> coercesArrayLitComplex l e1 es c2
        Nothing -> do
            c2 <- expandCTypeVar l v
            coercesArrayLitComplex l e1 es c2
coercesArrayLitComplex l e1 es1 t2@(ArrayLit es2) | length es1 == length es2 = do
    mapM_ (\(x,y) -> tcCstrM l $ Equals (IdxT x) (IdxT y)) $ zip (Foldable.toList es1) (Foldable.toList es2)
    return $ fmap (const $ ComplexT t2) e1
coercesArrayLitComplex l e1 es1 t2 = constraintError CoercionException l (ArrayLit es1) t2 Nothing  
    
coercesLitBase :: (VarsTcM loc,Location loc) => loc -> Literal () -> BaseType -> TcM loc ()
coercesLitBase l lit t2@(BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
       Just t2' -> coercesLitBase l lit t2'
       Nothing -> do
           b <- case lit of
                StringLit _ s -> return $ TyPrim $ DatatypeString ()
                BoolLit _ b -> return $ TyPrim $ DatatypeBool ()
                otherwise -> constraintError (\x y e -> Halt $ CoercionException x y e) l lit t2 Nothing
           addSubstM l (fmap (const BType) v) (BaseT b)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primIntBounds -> Just (min,max)))) = do
    unless (min <= i && i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primFloatBounds -> Just (min,max)))) = do
    unless (min <= fromInteger i && fromInteger i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLitBase l (FloatLit _ f) (TyPrim (t@(primFloatBounds -> Just (min,max)))) | isPrimFloat t = do
    unless (min <= f && f <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show f) (pp t) (show min) (show max)
coercesLitBase l (BoolLit _ b) (TyPrim (DatatypeBool _)) = return ()
coercesLitBase l (StringLit _ s) (TyPrim (DatatypeString _)) = return ()
coercesLitBase l l1 t2 = constraintError CoercionException l l1 t2 Nothing  

-- | Checks if a type is more specific than another, performing substitutions
compares :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc Ordering
compares l (IdxT e1) (IdxT e2) = comparesExpr l e1 e2
compares l (BaseT b1) (BaseT b2) = do
    comparesBase l b1 b2
compares l (ComplexT c1) (ComplexT c2) = do
    comparesComplex l c1 c2
compares l (BaseT b1) (ComplexT c2) = do
    comparesComplex l (defCType b1) c2
compares l (ComplexT c1) (BaseT b2) = do
    comparesComplex l c1 (defCType b2)
compares l (SecT s1) (SecT s2) = do
    comparesSec l s1 s2
compares l (SysT t1) (SysT t2) = do
    comparesSys l t1 t2
compares l (DecT d1) (DecT d2) = do
    comparesDec l d1 d2
compares l (CondType t1 c1) (CondType t2 c2) = do
    o1 <- compares l t1 t2
    o2 <- comparesSCond l c1 c2
    return $ o1 `mappend` o2
compares l (CondType t1 c1) t2 = do
    o1 <- compares l t1 t2
    o2 <- comparesSCond l c1 trueSCond
    return $ o1 `mappend` o2
compares l t1 (CondType t2 c2) = do
    o1 <- compares l t1 t2
    o2 <- comparesSCond l trueSCond c2
    return $ o1 `mappend` o2
compares l t1 t2 = addErrorM
    (TypecheckerError (locpos l) . ComparisonException (pp t1) (pp t2) . Right)
    (equals l t1 t2 >> return EQ)

decToken :: TcM loc DecType
decToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ DVar (VarName () v)

secToken :: TcM loc SecType
secToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ SVar (VarName () v) AnyKind
    
baseToken :: TcM loc BaseType
baseToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ BVar $ VarName () v

complexToken :: TcM loc ComplexType
complexToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    return $ CVar $ VarName () v

exprToken :: TcM loc (Expression VarIdentifier Type)
exprToken = do
    i <- newTyVarId
    let v = VarIdentifier "tok" (Just i) True
    let t = BaseT $ BVar $ VarName () v
    return $ RVariablePExpr t (VarName t v)

comparesDec :: (VarsTcM loc,Location loc) => loc -> DecType -> DecType -> TcM loc Ordering
comparesDec l t1@(DVar v1) t2@(DVar v2) | not (varTok v1) && not (varTok v2) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- decToken
            addSubst l v1 $ DecT x
            addSubst l v2 $ DecT x
            return EQ
        (Just t1',Nothing) -> comparesDec l t1' t2
        (Nothing,Just t2') -> comparesDec l t1 t2'
        (Just t1',Just t2') -> comparesDec l t1' t2'        
comparesDec l t1 (DVar v) | not (varTok v) = do
    mb <- tryResolveDVar l v
    case mb of
        Just t2 -> comparesDec l t1 t2
        Nothing -> do
            addSubst l v $ DecT t1
            return LT
comparesDec l (DVar v) t2 | not (varTok v) = do
    mb <- tryResolveDVar l v
    case mb of
        Just t1 -> comparesDec l t1 t2
        Nothing -> do
            addSubst l v $ DecT t2
            return GT
comparesDec l t1 t2 = addErrorM
    (TypecheckerError (locpos l) . ComparisonException (pp t1) (pp t2) . Right)
    (equalsDec l t1 t2 >> return EQ)

comparesSec :: (VarsTcM loc,Location loc) => loc -> SecType -> SecType -> TcM loc Ordering
comparesSec l Public Public = return EQ
comparesSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return EQ
comparesSec l Public (Private {}) = return LT -- public computations are preferrable
comparesSec l (Private {}) Public = return GT -- public computations are preferrable
comparesSec l t1@(SVar v1 k1) t2@(SVar v2 k2) | not (varTok v1) && not (varTok v2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> case (k1,k2) of
            (AnyKind,PrivateKind _) -> return GT
            (PrivateKind _,AnyKind) -> return LT
            (k1,(==k1) -> True) -> do
                x <- secToken
                addSubst l v1 $ SecT x
                addSubst l v2 $ SecT x
                return EQ
            otherwise -> constraintError ComparisonException l t1 t2 Nothing
        (Just t1',Nothing) -> comparesSec l t1' t2
        (Nothing,Just t2') -> comparesSec l t1 t2'
        (Just t1',Just t2') -> comparesSec l t1' t2'        
comparesSec l t1 (SVar v _) | not (varTok v) = do
    mb <- tryResolveSVar l v
    case mb of
        Just t2 -> comparesSec l t1 t2
        Nothing -> do
            addSubst l v $ SecT t1
            return LT
comparesSec l (SVar v _) t2 | not (varTok v) = do
    mb <- tryResolveSVar l v
    case mb of
        Just t1 -> comparesSec l t1 t2
        Nothing -> do
            addSubst l v $ SecT t2
            return GT
comparesSec l t1 t2 = constraintError ComparisonException l t1 t2 Nothing

comparesSys :: (VarsTcM loc,Location loc) => loc -> SysType -> SysType -> TcM loc Ordering
comparesSys l (SysPush t1) (SysPush t2) = do
    compares l t1 t2
comparesSys l (SysRet t1) (SysRet t2) = do
    compares l t1 t2
comparesSys l (SysRef t1) (SysRef t2) = do
    compares l t1 t2
comparesSys l (SysCRef t1) (SysCRef t2) = do
    compares l t1 t2
comparesSys l t1 t2 = constraintError ComparisonException l t1 t2 Nothing

comparesBase :: (VarsTcM loc,Location loc) => loc -> BaseType -> BaseType -> TcM loc Ordering
comparesBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2 >> return EQ
comparesBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2 >> return EQ
comparesBase l t1@(BVar v1) t2@(BVar v2) | not (varTok v1) && not (varTok v2) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- baseToken
            addSubst l v1 $ BaseT x
            addSubst l v2 $ BaseT x
            return EQ
        (Just t1',Nothing) -> comparesBase l t1' t2
        (Nothing,Just t2') -> comparesBase l t1 t2'
        (Just t1',Just t2') -> comparesBase l t1' t2'        
comparesBase l t1 (BVar v) | not (varTok v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> comparesBase l t1 t2
        Nothing -> do
            addSubst l v $ BaseT t1
            return LT
comparesBase l (BVar v) t2 | not (varTok v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> comparesBase l t1 t2
        Nothing -> do
            addSubst l v $ BaseT t2
            return GT
comparesBase l t1 t2 = constraintError ComparisonException l t1 t2 Nothing

comparesComplex :: (VarsTcM loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc Ordering
comparesComplex l Void Void = return EQ
comparesComplex l (TyLit lit1) (TyLit lit2) | lit1 == lit2 = return EQ
comparesComplex l t1@(TyLit lit) t2 = do
    let e1 = LitPExpr (ComplexT t1) $ fmap (const (ComplexT t1)) lit
    coercesLitComplex l e1 lit t2
    return GT
comparesComplex l t1 t2@(TyLit lit) = do
    let e2 = LitPExpr (ComplexT t2) $ fmap (const (ComplexT t2)) lit
    coercesLitComplex l e2 lit t1
    return LT
comparesComplex l ct1@(ArrayLit es1) ct2@(ArrayLit es2) = do
    if (length es1 == length es2)
        then do
            os <- mapM (\(x,y) -> liftM (Comparison x y) $ comparesExpr l x y) $ zip (Foldable.toList es1) (Foldable.toList es2)
            liftM compOrdering $ appendComparisons l os
        else return $ compare (length es1) (length es2)
comparesComplex l t1@(ArrayLit lit) t2 = do
    let e1 = ArrayConstructorPExpr (ComplexT t1) lit
    coercesArrayLitComplex l e1 lit t2
    return GT
comparesComplex l t1 t2@(ArrayLit lit) = do
    let e2 = ArrayConstructorPExpr (ComplexT t2) lit
    coercesArrayLitComplex l e2 lit t1
    return LT
comparesComplex l ct1@(CType s1 t1 d1 sz1) ct2@(CType s2 t2 d2 sz2) = do
    o1 <- liftM (Comparison s1 s2) $ comparesSec l s1 s2
    o2 <- liftM (Comparison t1 t2) $ comparesBase l t1 t2
    o3 <- liftM (Comparison d1 d2) $ comparesExpr l d1 d2
    os <- mapM (\(x,y) -> liftM (Comparison x y) $ comparesExpr l x y) =<< zipSizes l sz1 sz2
    liftM compOrdering $ appendComparisons l (o1:o2:o3:os)
comparesComplex l t1@(CVar v1) t2@(CVar v2) | not (varTok v1) && not (varTok v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- complexToken
            addSubst l v1 $ ComplexT x
            addSubst l v2 $ ComplexT x
            return EQ
        (Just t1',Nothing) -> comparesComplex l t1' t2
        (Nothing,Just t2') -> comparesComplex l t1 t2'
        (Just t1',Just t2') -> comparesComplex l t1' t2'        
comparesComplex l t1 (CVar v) | not (varTok v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just t2 -> comparesComplex l t1 t2
        Nothing -> do
            addSubst l v $ ComplexT t1
            return LT
comparesComplex l (CVar v) t2 | not (varTok v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just t1 -> comparesComplex l t1 t2
        Nothing -> do
            addSubst l v $ ComplexT t2
            return GT
comparesComplex l t1 t2 = constraintError ComparisonException l t1 t2 Nothing
    
comparesFoldable :: (VarsTcM loc,Foldable t,Location loc) => loc -> t Type -> t Type -> TcM loc Ordering
comparesFoldable l xs ys = comparesList l (toList xs) (toList ys)

data Comparison where
    Comparison :: IsComp a => a -> a -> Ordering -> Comparison
  deriving (Typeable)

type IsComp a = (Vars (TcM Position) a)
    
instance Data Comparison where
    gfoldl k z (Comparison x y o) = z Comparison `k` x `k` y `k` o
    gunfold k z c = error "gunfold Comparison"
    toConstr (Comparison {}) = con_Comparison
    dataTypeOf _ = ty_Comparison

con_Comparison = mkConstr ty_Comparison "Comparison" [] Prefix
ty_Comparison   = mkDataType "Language.SecreC.TypeChecker.Constraint.Comparison" [con_Comparison]
    
instance Eq Comparison where
    (Comparison x1 y1 o1) == (Comparison x2 y2 o2) = o1 == o2
instance Ord Comparison where
    compare (Comparison _ _ o1) (Comparison _ _ o2) = compare o1 o2
deriving instance Show Comparison

instance PP Comparison where
    pp (Comparison x y o) = pp x <+> pp o <+> pp y
instance Vars (TcM Position) Comparison where
    traverseVars f (Comparison x y o) = do
        x' <- f x
        y' <- f y
        o' <- f o
        return $ Comparison x' y' o'

compOrdering (Comparison _ _ o) = o
ppCompares x y o = pp x <+> pp o <+> pp y

comparesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc Ordering
comparesList l [] [] = return EQ
comparesList l a@(x:xs) b@(y:ys) = do
    f <- liftM (Comparison x y) $ compares l x y
    g <- liftM (Comparison xs ys) $ comparesList l xs ys
    liftM compOrdering $ appendComparison l f g
comparesList l xs ys = constraintError ComparisonException l xs ys Nothing
    
appendComparison :: (Location loc) => loc -> Comparison -> Comparison -> TcM loc Comparison
appendComparison l (Comparison x1 x2 EQ) y@(Comparison y1 y2 o) = return y
appendComparison l x@(Comparison x1 x2 o) (Comparison y1 y2 EQ) = return x
appendComparison l (Comparison x1 x2 LT) y@(Comparison y1 y2 LT) = return y
appendComparison l (Comparison x1 x2 GT) y@(Comparison y1 y2 GT) = return y
appendComparison l c1 c2 = constraintError ComparisonException l c1 c2 Nothing

appendComparisons l xs = foldr1M (appendComparison l) xs

-- | Non-directed unification, without implicit security coercions.
-- applies substitutions
unifies :: (VarsTcM loc,Location loc) => loc -> Type -> Type -> TcM loc ()
unifies l (IdxT e1) (IdxT e2) = unifiesExpr l e1 e2
unifies l (SecT s1) (SecT s2) = unifiesSec l s1 s2
unifies l (SysT s1) (SysT s2) = unifiesSys l s1 s2
unifies l (BaseT b1) (BaseT b2) = unifiesBase l b1 b2
unifies l (BaseT b1) (ComplexT c2) = unifiesComplex l (defCType b1) c2
unifies l (ComplexT c1) (BaseT b2) = unifiesComplex l c1 (defCType b2)
unifies l (ComplexT c1) (ComplexT c2) = unifiesComplex l c1 c2
unifies l (DecT d1) (DecT d2) = unifiesDec l d1 d2
unifies l t1@(CondType t1' c1) t2@(CondType t2' c2) = do
    unifies l t1' t2'
    unifiesSCond l c1 c2
unifies l t1@(CondType t1' c1) t2 = do
    unifies l t1' t2
    unifiesSCond l c1 trueSCond
unifies l t1 t2@(CondType t2' c2) = do
    unifies l t1 t2'
    unifiesSCond l trueSCond c2
unifies l t1 t2 = addErrorM
    (TypecheckerError (locpos l) . UnificationException (pp t1) (pp t2) . Right)
    (equals l t1 t2)

unifiesDec :: (VarsTcM loc,Location loc) => loc -> DecType -> DecType -> TcM loc ()
unifiesDec l d1@(DVar v1) d2@(DVar v2) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (DecT d1') (DecT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (DecT d1') (DecT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (DecT d1) (DecT d2')
        (Nothing,Nothing) -> addSubstM l (fmap (const DType) v1) (DecT d2)
unifiesDec l (DVar v) c2 = do
    mb <- tryResolveDVar l v
    case mb of
        Just c1 -> tcCstrM l $ Unifies (DecT c1) (DecT c2)
        Nothing -> addSubstM l (fmap (const DType) v) (DecT c2)
unifiesDec l c1 (DVar v) = do
    mb <- tryResolveDVar l v
    case mb of
        Just c2 -> tcCstrM l $ Unifies (DecT c1) (DecT c2)
        Nothing -> addSubstM l (fmap (const DType) v) (DecT c1)
unifiesDec l t1 t2 = addErrorM
    (TypecheckerError (locpos l) . UnificationException (pp t1) (pp t2) . Right)
    (equalsDec l t1 t2)

unifiesComplex :: (VarsTcM loc,Location loc) => loc -> ComplexType -> ComplexType -> TcM loc ()
unifiesComplex l Void Void = return ()
--unifiesComplex l t1@(TyLit lit) t2 = do
--    let e1 = LitPExpr (ComplexT t1) $ fmap (const $ ComplexT t1) lit
--    v2 <- newTypedVar $ ComplexT t2
--    coercesLitComplex l e1 lit v2 t2
--unifiesComplex l t1 (TyLit lit) = coercesLitComplex l lit t1
--unifiesComplex l t1@(ArrayLit es) t2 = coercesArrayLitComplex l es t2
--unifiesComplex l t1 (ArrayLit es) = coercesArrayLitComplex l es t1 >> return ()
unifiesComplex l (CType s1 t1 d1 sz1) (CType s2 t2 d2 sz2) = do
    tcCstrM l $ Unifies (SecT s1) (SecT s2)
    tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
    tcCstrM l $ Unifies (IdxT d1) (IdxT d2)
    mapM_ (\(x,y) -> tcCstrM l $ Unifies (IdxT x) (IdxT y)) =<< zipSizes l sz2 sz2
unifiesComplex l d1@(CVar v1) d2@(CVar v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (ComplexT d1') (ComplexT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (ComplexT d1') (ComplexT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (ComplexT d1) (ComplexT d2')
        (Nothing,Nothing) -> addSubstM l (fmap (const TType) v1) (ComplexT d2)
unifiesComplex l (CVar v) c2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just c1 -> tcCstrM l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (fmap (const TType) v) (ComplexT c2)
unifiesComplex l c1 (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> tcCstrM l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l (fmap (const TType) v) (ComplexT c1)
unifiesComplex l t1 t2 = constraintError UnificationException l t1 t2 Nothing

unifiesSVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> SVarKind -> SecType -> TcM loc ()
unifiesSVar l v k@AnyKind s1 = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind Nothing) s1@(Private _ _) = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind (Just n)) s1@(Private d ((==n) -> True)) = addSVarSubstM l v s1
unifiesSVar l v k s1@(SVar v1 k1) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> tcCstrM l $ Unifies (SecT $ SVar v k) (SecT s1')
        Nothing -> if k <= k1
            then addSVarSubstM l v s1
            else addSVarSubstM l v1 (SVar v k)
unifiesSVar l v k s = constraintError UnificationException l (SVar v k) s Nothing

addSVarSubstM l v s = addSubstM l (fmap (const $ SType $ secTypeKind s) v) (SecT s)

unifiesSec :: (VarsTcM loc,Location loc) => loc -> SecType -> SecType -> TcM loc ()
unifiesSec l Public Public = return ()
unifiesSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
unifiesSec l d1@(SVar v1 k1) d2@(SVar v2 k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (SecT d1') (SecT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (SecT d1') (SecT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (SecT d1) (SecT d2')
        (Nothing,Nothing) -> unifiesSVar l v1 k1 d2
unifiesSec l (SVar v k) s2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just s1 -> tcCstrM l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s2
unifiesSec l s1 (SVar v k) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2 -> tcCstrM l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s1
unifiesSec l t1 t2 = constraintError UnificationException l t1 t2 Nothing

unifiesSys :: (VarsTcM loc,Location loc) => loc -> SysType -> SysType -> TcM loc ()
unifiesSys l (SysPush t1) (SysPush t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l (SysRet t1) (SysRet t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l (SysRef t1) (SysRef t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l (SysCRef t1) (SysCRef t2) = do
    tcCstrM l $ Unifies t1 t2
unifiesSys l t1 t2 = constraintError UnificationException l t1 t2 Nothing

unifiesBase :: (VarsTcM loc,Location loc) => loc -> BaseType -> BaseType -> TcM loc ()
unifiesBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
unifiesBase l d1@(BVar v1) d2@(BVar v2) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM l $ Unifies (BaseT d1') (BaseT d2')
        (Just d1',Nothing) -> tcCstrM l $ Unifies (BaseT d1') (BaseT d2)
        (Nothing,Just d2') -> tcCstrM l $ Unifies (BaseT d1) (BaseT d2')
        (Nothing,Nothing) -> addSubstM l (fmap (const BType) v1) (BaseT d2)
unifiesBase l (BVar v) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (fmap (const BType) v) (BaseT t2)
unifiesBase l t1 (BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> tcCstrM l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l (fmap (const BType) v) (BaseT t1)
unifiesBase l (TyDec d1) (TyDec d2) = equalsDec l d1 d2
unifiesBase l t1 t2 = constraintError UnificationException l t1 t2 Nothing

unifiesSizes :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> Expression VarIdentifier Type -> [Expression VarIdentifier Type] -> TcM loc ()
unifiesSizes l dim1 szs1 dim2 szs2 = do
    mapM_ (\(x,y) -> tcCstrM l $ Unifies (IdxT x) (IdxT y)) =<< zipSizes l szs1 szs2

unifiesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    tcCstrM l $ Unifies x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError UnificationException l xs ys Nothing

resolveCVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc ComplexType
resolveCVar l v = resolveTVar l v >>= typeToComplexType l

resolveSVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc SecType
resolveSVar l v = resolveTVar l v >>= typeToSecType l

resolveDVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc DecType
resolveDVar l v = resolveTVar l v >>= typeToDecType l

resolveBVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc BaseType
resolveBVar l v = resolveTVar l v >>= typeToBaseType l

resolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> do
            ss <- getTSubsts
            vs <- fvIds v
            env <- liftM ppTSubsts $ filterTSubsts vs ss
            tcError (locpos l) $ Halt $ UnresolvedVariable (pp v) env
        Just t -> return t

tryResolveSVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc (Maybe SecType)
tryResolveSVar l v = tryResolveTVar l v >>= mapM (typeToSecType l)

tryResolveBVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc (Maybe BaseType)
tryResolveBVar l v = tryResolveTVar l v >>= mapM (typeToBaseType l)

tryResolveCVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc (Maybe ComplexType)
tryResolveCVar l v = tryResolveTVar l v >>= mapM (typeToComplexType l)

tryResolveDVar :: (VarsTcM loc,Location loc) => loc -> VarName VarIdentifier () -> TcM loc (Maybe DecType)
tryResolveDVar l v = tryResolveTVar l v >>= mapM (typeToDecType l)

-- | tries to resolve a type variable by looking its value in the substitutions and in the environment
tryResolveTVar :: Location loc => loc -> VarName VarIdentifier () -> TcM loc (Maybe Type)
tryResolveTVar l v = do
    addVarDependencies (varNameId v)
    -- lookup in the substitution environment
    s <- liftM (tSubsts . mconcatNe . tDict) State.get
    mb <- substsFromMap s $ v
    return $ mb

setCSec (CType _ t d sz) s = CType s t d sz

isSupportedPrint :: (VarsTcM loc,Location loc) => loc -> [Expression VarIdentifier Type] -> [VarName VarIdentifier Type] -> TcM loc ()
isSupportedPrint l ts xs = forM_ (zip ts xs) $ \(t,x) -> do
    (dec,[y]) <- tcTopPDecCstrM l True (Left $ ProcedureName () (mkVarId "tostring")) Nothing [t] (BaseT string)
    unifiesExpr l (varExpr x) y
    return ()

isReturnStmt :: (VarsTcM loc,Location loc) => loc -> Set StmtClass -> Type -> ProcedureDeclaration VarIdentifier Position -> TcM loc ()
isReturnStmt l cs ret dec = aux $ Set.toList cs
    where
    aux [StmtReturn] = return ()
    aux c = mapError (\err -> TypecheckerError (locpos l) $ NoReturnStatement $ pp dec) (tcCstrM l (Unifies (ComplexT Void) ret) >> return ())

unifiesSCond :: (VarsTcM loc,Location loc) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM loc ()
unifiesSCond l e1 e2 = unifiesExpr l e1 e2 `mplus` satisfiesSConds l [e1,e2]

satisfiesSConds :: (VarsTcM loc,Location loc) => loc -> [SCond VarIdentifier Type] -> TcM loc ()
satisfiesSConds l is = do
    cs <- mapM (expr2ICond . fmap (Typed l)) is
    checkCstrM l $ IsValid $ IAnd cs

unifiesExpr :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc ()
unifiesExpr l e1@(RVariablePExpr _ v1@(VarName _ n)) e2@(RVariablePExpr _ v2) = do
    mb1 <- tryResolveEVar l (funit v1)
    mb2 <- tryResolveEVar l (funit v2)
    case (mb1,mb2) of
        (Just e1',Just e2') -> unifiesExpr l (fmap typed e1') (fmap typed e2')
        (Just e1',Nothing) -> unifiesExpr l (fmap typed e1') e2
        (Nothing,Just e2') -> unifiesExpr l e1 (fmap typed e2')
        (Nothing,Nothing) -> addValueM l v1 e2
unifiesExpr l (RVariablePExpr _ v1) e2 = do
    mb <- tryResolveEVar l (funit v1)
    case mb of
        Nothing -> addValueM l v1 e2
        Just e1' -> unifiesExpr l (fmap typed e1') e2
unifiesExpr l e1 (RVariablePExpr _ v2) = do
    mb <- tryResolveEVar l (funit v2)
    case mb of
        Nothing -> addValueM l v2 e1
        Just e2' -> unifiesExpr l e1 (fmap typed e2')
unifiesExpr l e1 e2 = equalsExpr l e1 e2
    
unifiesTIdentifier :: (VarsTcM loc,Location loc) => loc -> TIdentifier -> TIdentifier -> TcM loc ()
unifiesTIdentifier l (Right (Right (OpCast _ t1))) (Right (Right (OpCast _ t2))) = do
    unifies l (castTypeToType t1) (castTypeToType t2)
unifiesTIdentifier l (Right (Right op1)) (Right (Right op2)) | funit op1 == funit op2 = return ()
unifiesTIdentifier l n1 n2 | n1 == n2 = return ()
unifiesTIdentifier l t1 t2 = constraintError UnificationException l t1 t2 Nothing
    
equalsSCond :: (VarsTcM loc,Location loc) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM loc ()
equalsSCond l e1 e2 = do
    equalsExpr l e1 e2
    
comparesSCond :: (VarsTcM loc,Location loc) => loc -> SCond VarIdentifier Type -> SCond VarIdentifier Type -> TcM loc Ordering
comparesSCond l (e1) (e2) = mplus
    (comparesExpr l e1 e2)
    (do
        i1 <- expr2ICond $ fmap (Typed l) e1
        i2 <- expr2ICond $ fmap (Typed l) e2
        compareICond l i1 i2)
    
comparesExpr :: (VarsTcM loc,Location loc) => loc -> Expression VarIdentifier Type -> Expression VarIdentifier Type -> TcM loc Ordering
comparesExpr l e1@(RVariablePExpr _ v1@(VarName _ n)) e2@(RVariablePExpr _ v2) | not (varTok v1) && not (varTok v2) = do
    mb1 <- tryResolveEVar l (funit v1)
    mb2 <- tryResolveEVar l (funit v2)
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- exprToken
            addValue l v1 x
            addValue l v2 x
            return EQ
        (Just e1',Nothing) -> comparesExpr l (fmap typed e1') e2
        (Nothing,Just e2') -> comparesExpr l e1 (fmap typed e2')
        (Just e1',Just e2') -> comparesExpr l (fmap typed e1') (fmap typed e2')
comparesExpr l (RVariablePExpr _ v1) e2 | not (varTok v1) = do
    mb <- tryResolveEVar l (funit v1)
    case mb of
        Nothing -> do
            addValue l v1 e2
            return GT
        Just e1' -> comparesExpr l (fmap typed e1') e2
comparesExpr l e1 (RVariablePExpr _ v2) | not (varTok v2) = do
    mb <- tryResolveEVar l (funit v2)
    case mb of
        Nothing -> do
            addValue l v2 e1
            return LT
        Just e2' -> comparesExpr l e1 (fmap typed e2')
comparesExpr l e1 e2 = equalsExpr l e1 e2 >> return EQ
    
constraintError :: (Vars (TcM Position) a,Vars (TcM Position) b,Location loc) => (Doc -> Doc -> Either Doc SecrecError -> TypecheckerErr) -> loc -> a -> b -> Maybe SecrecError -> TcM loc res
constraintError k l e1 e2 (Just suberr) = do
    tcError (locpos l) $ k (pp e1) (pp e2) $ Right suberr
constraintError k l e1 e2 Nothing = do
    vs1 <- tcPos $ fvIds e1
    vs2 <- tcPos $ fvIds e2
    let vs = Set.union vs1 vs2
    ss <- getTSubsts
    ss' <- filterTSubsts vs ss
    tcError (locpos l) $ k (pp e1) (pp e2) $ Left $ ppTSubsts ss'
    
--coercesList :: (VarsTcM loc,Location loc) => loc -> [Type] -> [Type] -> TcM loc ()
--coercesList l [] [] = return ()
--coercesList l (x:xs) (y:ys) = do
--    tcCstrM l $ Coerces x y
--    coercesList l xs ys
--coercesList l xs ys = constraintError CoercionException l xs ys Nothing

constraintList :: (VarsTcM loc,Location loc,Vars (TcM Position) [a],Vars (TcM Position) [b]) =>
    (Doc -> Doc -> Either Doc SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM loc x) -> loc -> [a] -> [b] -> TcM loc [x]
constraintList err f l [] [] = return []
constraintList err f l (x:xs) (y:ys) = do
    r <- f x y
    rs <- constraintList err f l xs ys
    return (r:rs)
constraintList err f l xs ys = constraintError err l xs ys Nothing

checkAssertion :: (Vars (TcM loc) loc,Location loc) => loc -> Expression VarIdentifier Type -> TcM loc ()
checkAssertion l e = addErrorM (TypecheckerError (locpos l) . StaticAssertionFailure (pp e)) $ orWarn_ $ do
    ic <- expr2ICond $ fmap (Typed l) e
    isValid l ic

tcTopCoercesCstrM :: (Vars (TcM loc) loc,Location loc) => loc -> Expression VarIdentifier Type -> Type -> VarName VarIdentifier Type -> Type -> TcM loc ()
tcTopCoercesCstrM l e1 t1 x2 t2 = do
    opts <- askOpts
    unless (implicitClassify opts) $ unifiesExpr l (varExpr x2) e1
    tcTopCstrM l $ Coerces e1 t1 x2 t2

tcTopCoerces2CstrM :: (Vars (TcM loc) loc,Location loc) => loc -> Expression VarIdentifier Type -> Type -> Expression VarIdentifier Type -> Type -> VarName VarIdentifier Type -> VarName VarIdentifier Type -> Type -> TcM loc ()
tcTopCoerces2CstrM l e1 t1 e2 t2 x1 x2 t3 = do
    opts <- askOpts
    unless (implicitClassify opts) $ unifiesExpr l (varExpr x2) e1
    tcTopCstrM l $ Coerces2 e1 t1 e2 t2 x1 x2 t3

tcTopPDecCstrM :: Location loc => loc -> Bool -> PIdentifier -> (Maybe [Type]) -> [Expression VarIdentifier Type] -> Type -> TcM loc (DecType,[Expression VarIdentifier Type])
tcTopPDecCstrM l doCoerce pid targs es tret = do
    dec <- newDecVar
    opts <- askOpts
    if (doCoerce && implicitClassify opts)
        then do
            xs <- replicateM (length es) $ do
                tx <- newTyVar
                x <- newTypedVar tx
                return x
            tcTopCstrM l $ PDec pid targs es tret dec $ Just xs
            let es' = map varExpr xs
            return (dec,es')
        else do
            tcTopCstrM l $ PDec pid targs es tret dec Nothing
            return (dec,es)