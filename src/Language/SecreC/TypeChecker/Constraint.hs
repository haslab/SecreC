{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, ConstraintKinds, StandaloneDeriving, DeriveDataTypeable, MultiParamTypeClasses, TupleSections, GADTs, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Template
import {-# SOURCE #-} Language.SecreC.Prover.Expression
import Language.SecreC.Prover.Semantics
import Language.SecreC.Prover.SMT
import Language.SecreC.Prover.Base
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Pretty
import Language.SecreC.Utils

import Control.Monad
import Control.Monad.Except
import qualified Control.Monad.State as State
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.Writer as Writer
import Control.Monad.RWS as RWS hiding ((<>))

import Data.Word
import Data.Bifunctor
import Data.Either
import Data.Hashable
import Data.Monoid hiding ((<>))
import Data.Unique
import Data.Maybe
import Data.Foldable as Foldable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Data hiding (cast)
import qualified Data.Map as Map
import Data.Generics hiding (LT,GT,cast,typeOf)
import qualified Data.Generics as Generics
import Data.List as List
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.Graph.Inductive.Query.TransClos as Graph

import Text.PrettyPrint as PP hiding (equals)

import Safe

-- * Constraint Engine

-- solves all hypotheses in the environment
solveHypotheses :: (ProverK loc m) => loc -> TcM m [IExpr]
solveHypotheses l = do
    hyps <- liftM Set.toList getHyps
    (_,dhyps) <- tcWith (locpos l) "solveHypotheses" $ do
        addHeadTCstrs l $ Graph.insNodes (map (\x -> (ioCstrId $ unLoc x,x)) hyps) Graph.empty
        solve l "solveHypotheses"
    addHeadTDict l $ dhyps { tCstrs = Graph.empty }
    -- collect the result for the hypotheses
    liftM concat $ forM hyps $ \(Loc _ iok) -> do
        liftM (maybeToList . join) $ ioCstrResult l iok proxy
  where proxy = Proxy :: Proxy (Maybe IExpr)

-- | solves the whole constraint stack
solveAll :: ProverK loc m => loc -> String -> TcM m ()
solveAll l msg = do
    depth <- liftM (length . tDict) State.get
    replicateM_ depth $ do
        solve' l msg True
        env <- State.get
        dicts' <- mergeHeadDict l (tDict env)
        State.put $ env { tDict = dicts' }
    State.modify $ \env -> env { tDict = (replicate (depth - 1) emptyTDict) ++ tDict env }

mergeHeadDict :: ProverK loc m => loc -> [TDict] -> TcM m [TDict]
mergeHeadDict l [] = return []
mergeHeadDict l [x] = return [x]
mergeHeadDict l (x:y:xs) = do
    xy <- appendTDict l NoCheckS x y
    return (xy:xs)

solve :: ProverK loc m => loc -> String -> TcM m ()
solve l msg = solve' l msg False

-- | solves all constraints in the top environment
solve' :: (ProverK loc m) => loc -> String -> Bool -> TcM m ()
solve' l msg failOnError = do
    mb <- solveMb l msg failOnError
    case mb of
        Nothing -> return ()
        Just err -> throwError err

solveMb :: (ProverK loc m) => loc -> String -> Bool -> TcM m (Maybe SecrecError)
solveMb l msg failOnError = do
    gr <- liftM (tCstrs . head . tDict) State.get
    if Graph.isEmpty gr
        then return Nothing
        else newErrorM $ tcNoDeps $ do
            --liftIO $ putStrLn $ "solving " ++ msg ++ " " ++ ppr l
            gr' <- buildCstrGraph l $ flattenIOCstrGraphSet gr
            updateHeadTCstrs $ \d -> return ((),gr')
            --ss <- ppConstraints gr
            --env <- State.get
            --liftIO $ putStrLn $ "solve " ++ show msg ++ " " ++ ppr l ++ " " ++ show (inTemplate env) ++ " [" ++ show ss ++ "\n]"
            mb <- solveCstrs l msg failOnError
            --liftIO $ putStrLn $ "solved " ++ show msg ++ " " ++ ppr l
            updateHeadTCstrs $ \d -> return ((),Graph.nfilter (`elem` Graph.nodes gr) d)
            --liftIO $ putStrLn $ "solved " ++ msg ++ " " ++ ppr l ++ ppr (isJust mb)
            return mb

priorityRoots :: (x,LocIOCstr) -> (x,LocIOCstr) -> Ordering
priorityRoots x y = priorityTCstr (kCstr $ unLoc $ snd x) (kCstr $ unLoc $ snd y)

solveCstrs :: (ProverK loc m) => loc -> String -> Bool -> TcM m (Maybe SecrecError)
solveCstrs l msg failOnError = do
    --dicts <- liftM tDict State.get
    --let dict = head dicts
    --ss <- ppConstraints (tCstrs dict)
    --liftIO $ putStrLn $ (concat $ replicate (length dicts) ">") ++ "solveCstrs " ++ show msg ++ " " ++ ppr l ++ " [" ++ show ss ++ "\n]"
    --doc <- liftM ppTSubsts $ getTSubsts l
    --liftIO $ putStrLn $ show doc
    gr <- liftM (tCstrs . head . tDict) State.get
    if (Graph.isEmpty gr)
        then return Nothing
        else do
            let roots = sortBy priorityRoots $ rootsGr gr -- sort by constraint priority
            when (List.null roots) $ error $ "solveCstrs: no root constraints to proceed"
            --liftIO $ putStrLn $ "solveCstrsG [" ++ show (sepBy space $ map (pp . ioCstrId . unLoc . snd) roots) ++ "\n]"
            go <- trySolveSomeCstrs failOnError $ map snd roots
            case go of
                Left _ -> solveCstrs l msg failOnError
                Right errs -> guessError errs

-- Left True = one constraint solved
-- Left False = no remaining unsolved constraints
-- Right err = failed
type SolveRes = Either Bool [(Unique,TCstr,SecrecError)]

mergeSolveRes :: SolveRes -> SolveRes -> SolveRes
mergeSolveRes (Left True) b = Left True
mergeSolveRes (Left False) b = b
mergeSolveRes a (Left True) = Left True
mergeSolveRes a (Left False) = a
mergeSolveRes (Right a) (Right b) = Right (a ++ b)

isErrorSolveRes :: SolveRes -> Bool
isErrorSolveRes (Left _) = False
isErrorSolveRes (Right es) = any (not . isHaltError . thr3) es

-- | tries to solve one or more constraints
trySolveSomeCstrs :: (ProverK Position m) => Bool -> [LocIOCstr] -> TcM m SolveRes
trySolveSomeCstrs failOnError = foldlM solveBound (Left False)
    where
    solveBound b x@(Loc l iok) = do
        if failOnError && isErrorSolveRes b
            then return b
            else do
                doAll <- getDoAll
                ok <- trySolveCstr doAll x
                return (mergeSolveRes b ok)

getErrors :: [(Unique,TCstr,SecrecError)] -> [SecrecError]
getErrors = map thr3 . flattenErrors
    
flattenErrors :: [(Unique,TCstr,SecrecError)] -> [(Unique,TCstr,SecrecError)]
flattenErrors [] = []
flattenErrors ((x,y,MultipleErrors errs):xs) = flattenErrors (map (\e -> (x,y,e)) errs ++ xs)
flattenErrors (err:xs) = err : flattenErrors xs

-- gets the first group of possible multiple substitutions from a set constraint errors
--getOpts :: (ProverK loc m) => loc -> [(Unique,TCstr,SecrecError)] -> TcM m (Maybe [TSubsts])
--getOpts l [] = return Nothing
--getOpts l ((u,x,y):xs) = case errorOpts x of
--    Just opts -> do
--        done <- isChoice l u
--        if done
--            then getOpts l xs
--            else do
--                addChoice u
--                return $ Just opts
--    otherwise -> getOpts l xs

--errorOpts :: TCstr -> Maybe [TSubsts]
--errorOpts = everything append (mkQ Nothing aux)
--    where
--    aux :: TCstr -> Maybe [TSubsts]
--    aux (TcK (MultipleSubstitutions v opts)) = Just $ map (TSubsts . Map.singleton v . fst) opts
--    aux _ = Nothing
--    append Nothing y = y
--    append x y = x
    
filterErrors :: (ProverK Position m) => Bool -> [(Unique,TCstr,SecrecError)] -> TcM m ([(Unique,TCstr,SecrecError)])
filterErrors False errs = do
    errs1 <- filterWarnings errs
    let errs2 = flattenErrors $ filter (not . isGlobalCstr . snd3) errs1
    let errs3 = filter (not . isHaltError . thr3) errs2
    let errs4 = filter (not . isHypCstr . snd3) errs3
    return errs4
filterErrors True errs = do
    errs1 <- filterWarnings errs
    errs2 <- filterMultipleSubsts errs1
    return errs2

filterWarnings :: (ProverK Position m) => [(Unique,TCstr,SecrecError)] -> TcM m [(Unique,TCstr,SecrecError)]
filterWarnings = filterM $ \(i,k,err) -> if isOrWarnError err
    then do
        errWarn err
        removeCstr i
        return False
    else return True

-- we let multiple substitution constraints go through if we are not solving the last dictionary, since these constraints can always be resolved at a later time
filterMultipleSubsts :: (ProverK Position m) => [(Unique,TCstr,SecrecError)] -> TcM m [(Unique,TCstr,SecrecError)]
filterMultipleSubsts errs = do
    dicts <- liftM tDict State.get
    if length dicts > 1
        then return $ filter (not . isMultipleSubstsCstr . snd3) errs
        else return errs

guessError :: (ProverK Position m) => [(Unique,TCstr,SecrecError)] -> TcM m (Maybe SecrecError)
guessError errs = do
    doAll <- getDoAll
    dicts <- liftM tDict State.get
    errs' <- filterErrors (doAll && length dicts > 1) errs
    if null errs' then return Nothing else return $ Just (MultipleErrors $ getErrors errs')

--guessCstrs :: (ProverK loc m) => loc -> Bool -> [(Unique,TCstr,SecrecError)] -> TcM m ()
--guessCstrs l False errs = guessError False errs
--guessCstrs l True errs = do
--    mb <- getOpts errs
--    case mb of
--        Nothing -> guessError True errs
--        Just opts -> do
--            tries <- steps opts
--            unless (List.null tries) $ throwError $ Halt $ TypecheckerError (locpos l) $ MultipleTypeSubstitutions tries
--  where
--    tryStep o e = text "Tried substitution:" <+> quotes (pp o) $+$ text "Sub-error:" <+> pp e
--    steps [] = return []
--    steps (o:os) = do
--        tryO <- step o
--        case tryO of
--            Nothing -> return []
--            Just err -> liftM (err:) (steps os)
--    step o = (do
----        ss <- ppConstraints =<< liftM (headNe . tDict) State.get
----        liftIO $ putStrLn $ "guessStep [" ++ show ss ++ "\n]" ++ ppr o
--        addSubsts o
--        solveCstrs l
--        return Nothing) `catchError` \e -> return (Just $ tryStep o e)

-- since templates are only resolved at instantiation time, we prevent solving of overloadable constraints
trySolveCstr :: (ProverK Position m) => Bool -> LocIOCstr -> TcM m SolveRes
trySolveCstr False (Loc l iok) | isGlobalCstr (kCstr iok) = do
    return $ Right [(uniqId $ kStatus iok,kCstr iok,TypecheckerError (locpos l) $ Halt $ GenTcError $ text "Unsolved global constraint")]
trySolveCstr doAll (Loc l iok) = catchError
    (solveIOCstr l iok >> return (Left True))
    (\e -> return $ Right [(uniqId $ kStatus iok,kCstr iok,e)])

solveIOCstr :: (ProverK loc m) => loc -> IOCstr -> TcM m ShowOrdDyn
solveIOCstr l iok = newErrorM $ resolveIOCstr l iok $ \k -> do
    --liftIO $ putStrLn $ "solveIOCstr " ++ ppr iok
    gr <- liftM (tCstrs . head . tDict) State.get
    let (ins,_,_,outs) = fromJustNote ("solveCstrNodeCtx " ++ ppr iok) $ contextGr gr (ioCstrId iok)
    let ins'  = map (fromJustNote "ins" . Graph.lab gr . snd) ins
    let outs' = map (fromJustNote "outs" . Graph.lab gr . snd) outs
    (res,rest) <- tcWith (locpos l) ("solveIOCstr " ++ ppr iok) $ resolveTCstr l k
    addHeadTDict l $ rest { tCstrs = Graph.empty }
    unless (Graph.isEmpty $ tCstrs rest) $ do
        --doc <- ppConstraints $ tCstrs rest
        --liftIO $ putStrLn $ "solvedIOCstr " ++ ppr (ioCstrId iok) ++ " -->" ++ show doc
        replaceCstrWithGraph l False (ioCstrId iok) (Set.fromList ins') (tCstrs rest) (Set.fromList outs')
    return res

-- * Throwing Constraints

tCstrM_ :: ProverK loc m => loc -> TCstr -> TcM m ()
tCstrM_ l (TcK c isAnn isPure) = withAnn isAnn $ withPure isPure $ tcCstrM_ l c
tCstrM_ l (CheckK c isAnn isPure) = withAnn isAnn $ withPure isPure $ checkCstrM_ l Set.empty c
tCstrM_ l (HypK c isAnn isPure) = withAnn isAnn $ withPure isPure $ hypCstrM_ l c
tCstrM_ l (DelayedK c arr) = addErrorM'' l arr (tCstrM_ l c)

checkCstrM_ :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m ()
checkCstrM_ l deps k = checkCstrM l deps k >> return ()

checkCstrM :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m (Maybe IOCstr)
checkCstrM l deps k | isTrivialCheckCstr k = return Nothing
checkCstrM l deps k = withDeps LocalScope $ do
    addDeps LocalScope deps
    isAnn <- getAnn
    isPure <- getPure
    newTCstr l $ CheckK k isAnn isPure

topCheckCstrM_ :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m ()
topCheckCstrM_ l deps k = newErrorM $ checkCstrM_ l deps k

topCheckCstrM :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m (Maybe IOCstr)
topCheckCstrM l deps k = newErrorM $ checkCstrM l deps k

hypCstrM_ :: (ProverK loc m) => loc -> HypCstr -> TcM m ()
hypCstrM_ l k = hypCstrM l k >> return ()

hypCstrM :: (ProverK loc m) => loc -> HypCstr -> TcM m (Maybe IOCstr)
hypCstrM l k | isTrivialHypCstr k = return Nothing
hypCstrM l k = do
    isAnn <- getAnn
    isPure <- getPure
    newTCstr l $ HypK k isAnn isPure

topHypCstrM_ :: (ProverK loc m) => loc -> HypCstr -> TcM m ()
topHypCstrM_ l k = newErrorM $ hypCstrM_ l k

topHypCstrM :: (ProverK loc m) => loc -> HypCstr -> TcM m (Maybe IOCstr)
topHypCstrM l k = newErrorM $ hypCstrM l k

tcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()
tcCstrM_ l k = tcCstrM l k >> return ()

tcCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM m (Maybe IOCstr)
tcCstrM l k | isTrivialTcCstr k = return Nothing
tcCstrM l k = do
--    liftIO $ putStrLn $ "tcCstrM " ++ ppr l ++ " " ++ ppr k
    isAnn <- getAnn
    isPure <- getPure
    k <- newTCstr l $ TcK k isAnn isPure
--    ss <- getTSubsts l
--    liftIO $ putStrLn $ "tcCstrMexit " ++ ppr l ++ " " ++ ppr ss
    return k

topTcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()
topTcCstrM_ l k = newErrorM $ tcCstrM_ l k
    
newTCstr :: (ProverK loc m) => loc -> TCstr -> TcM m (Maybe IOCstr)
newTCstr l k = do
    deps <- getDeps
    (i,delay) <- askErrorM'
    let k' = DelayedK k (i,SecrecErrArr delay)
    iok <- newTemplateConstraint l k'
    addIOCstrDependenciesM True deps (Loc (locpos l) iok) Set.empty
    
    if (isGlobalCstr k)
        then return Nothing
        else catchError
            (newErrorM $ resolveIOCstr l iok (resolveTCstr l) >> return Nothing)
            (\e -> if (isHaltError e) then return (Just iok) else throwError e)
                
resolveTCstr :: (ProverK loc m) => loc -> TCstr -> TcM m ShowOrdDyn
resolveTCstr l (TcK k isAnn isPure) = liftM ShowOrdDyn $ withDeps GlobalScope $ withAnn isAnn $ withPure isPure $ do
    resolveTcCstr l k
resolveTCstr l (HypK h isAnn isPure) = liftM ShowOrdDyn $ withDeps GlobalScope $ withAnn isAnn $ withPure isPure $ do
    resolveHypCstr l h
resolveTCstr l (CheckK c isAnn isPure) = liftM ShowOrdDyn $ withDeps GlobalScope $ withAnn isAnn $ withPure isPure $ do
    resolveCheckCstr l c
resolveTCstr l (DelayedK k (i,SecrecErrArr err)) = addErrorM' l (i,err) $ resolveTCstr l k

-- tests if a constraint is only used as part of an hypothesis
--isHypInGraph :: Int -> IOCstrGraph loc -> Bool
--isHypInGraph kid gr = case Graph.match kid gr of
--    (Nothing,gr') -> False
--    (Just (_,_,(kCstr . unLoc) -> HypK {},_),gr') -> True
--    (Just (_,_,_,outs),gr') -> all (flip isHypInGraph gr' . snd) outs

resolveTcCstr :: (ProverK loc m) => loc -> TcCstr -> TcM m ()
resolveTcCstr l k = do
--    gr <- liftM (tCstrs . headNe . tDict) State.get
--    let warn = isHypInGraph kid gr
--    liftIO $ putStrLn $ "resolve " ++ show warn ++ " " ++ ppr k
--    if warn then newErrorM $ orWarn_ $ resolveTcCstr' k else 
    resolveTcCstr' k
  where
    resolveTcCstr' k@(TDec n args x) = addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp n <+> parens (sepBy comma $ map pp args)))) $ do
        res <- matchTemplate l True (Left n) (Just args) Nothing Nothing [] (checkTemplateType $ fmap (const l) n)
        tcCstrM_ l $ Unifies (DecT x) (DecT res)
    resolveTcCstr' k@(PDec (Left n) specs args r x doCoerce xs) = addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp r <+> pp n <+> parens (sepBy comma $ map pp args)))) $ do
        isAnn <- getAnn
        res <- matchTemplate l doCoerce (Right $ Left n) specs (Just args) (Just r) xs (checkProcedure isAnn $ ProcedureName l n)
        --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
        --liftIO $ putStrLn $ "matchTemplate " ++ ppr n ++ " " ++ show doc
        tcCstrM_ l $ Unifies (DecT x) (DecT res)
        --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
        --liftIO $ putStrLn $ "matchTemplate2 " ++ ppr n ++ " " ++ show doc
    resolveTcCstr' k@(PDec (Right o) specs args r x doCoerce xs) = addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (pp r <+> pp o <+> parens (sepBy comma $ map pp args)))) $ do
        isAnn <- getAnn
        res <- matchTemplate l doCoerce (Right $ Right o) specs (Just args) (Just r) xs (checkOperator isAnn $ fmap (const l) o)
        --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
        --liftIO $ putStrLn $ "matchTemplate " ++ ppr o ++ " " ++ show doc
        tcCstrM_ l $ Unifies (DecT x) (DecT res)
        --doc <- ppConstraints =<< liftM (tCstrs . head . tDict) State.get
        --liftIO $ putStrLn $ "matchTemplate2 " ++ ppr o ++ " " ++ show doc
    resolveTcCstr' k@(Equals t1 t2) = do
        equals l t1 t2
    resolveTcCstr' k@(Coerces e1 x2) = do
        coerces l (tokenizeExpr e1) x2
    resolveTcCstr' k@(Coerces2 e1 e2 x1 x2) = do
        coerces2 l (tokenizeExpr e1) (tokenizeExpr e2) x1 x2
    resolveTcCstr' k@(CoercesLit e) = do
        coercesLit l e
    resolveTcCstr' k@(CoercesSecDimSizes e1 x2) = do
        coercesSecDimSizes l (tokenizeExpr e1) x2
    resolveTcCstr' k@(Coerces2SecDimSizes e1 e2 x1 x2) = do
        coerces2SecDimSizes l (tokenizeExpr e1) (tokenizeExpr e2) x1 x2
    resolveTcCstr' k@(Unifies t1 t2) = do
        unifies l t1 t2
    resolveTcCstr' k@(UnifiesSizes szs1 szs2) = do
        unifiesSizes l szs1 szs2
    resolveTcCstr' k@(TypeBase t x) = do
        BaseT b <- typeBase l t
        unifiesBase l b x
    resolveTcCstr' k@(SupportedPrint t xs) = do
        isSupportedPrint l t xs
    resolveTcCstr' k@(ProjectStruct t a x) = do
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedFieldProjection (pp t) (pp a <+> char '=' <+> pp x))
            (projectStructField l t a >>= \res -> tcCstrM_ l $ Unifies x res)
    resolveTcCstr' k@(ProjectMatrix ct rngs x) = do
        ct' <- ppM l ct
        rngs' <- ppArrayRangesM l rngs
        x' <- ppM l x
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedMatrixProjection ct' (brackets rngs' <+> char '=' <+> x'))
            (projectMatrixType l ct rngs >>= \res -> tcCstrM_ l $ Unifies x res)
    resolveTcCstr' (MultipleSubstitutions v s) = do
        multipleSubstitutions l v s
    resolveTcCstr' (MatchTypeDimension t d) = matchTypeDimension l t d
    resolveTcCstr' (IsValid c) = do
        x <- ppM l c
        addErrorM l (TypecheckerError (locpos l) . IndexConditionNotValid x) $ do
            ic <- prove l "resolve isValid" $ expr2IExpr $ fmap (Typed l) c
            isValid l ic
    resolveTcCstr' (NotEqual e1 e2) = do
        x <- ppM l e1
        y <- ppM l e2
        addErrorM l (TypecheckerError (locpos l) . IndexConditionNotValid (x <+> text "==" <+> y)) $ do
            i1 <- prove l "resolve notEqual" $ expr2IExpr $ fmap (Typed l) e1
            i2 <- prove l "resolve notEqual" $ expr2IExpr $ fmap (Typed l) e2
            isValid l $ IBinOp INeq i1 i2
    resolveTcCstr' (IsPublic e) = do
        ct <- typeToComplexType l (loc e)
        s <- cSecM l ct
        unifiesSec l s Public

resolveHypCstr :: (ProverK loc m) => loc -> HypCstr -> TcM m (Maybe IExpr)
resolveHypCstr l hyp = do
    doAll <- getDoAll
    if not doAll -- if we don't need to solve all constraints we accept no less than solving the hypothesis
        then newErrorM $ addErrorM l (TypecheckerError (locpos l) . FailAddHypothesis (pp hyp)) $ orWarn $ resolveHypCstr' hyp
        else liftM Just $ resolveHypCstr' hyp
  where
    resolveHypCstr' (HypCondition c) = expr2IExpr $ fmap (Typed l) c
    resolveHypCstr' (HypNotCondition c) = liftM (IUnOp INot) $ expr2IExpr $ fmap (Typed l) c
    resolveHypCstr' (HypEqual e1 e2) = do
        i1 <- expr2IExpr $ fmap (Typed l) e1
        i2 <- expr2IExpr $ fmap (Typed l) e2
        return $ IBinOp (IEq) i1 i2
    
resolveCheckCstr :: (ProverK loc m) => loc -> CheckCstr -> TcM m ()
resolveCheckCstr l k = addErrorM l (OrWarn . TypecheckerError (locpos l) . StaticAssertionFailure (pp k)) $ do
    resolveCheckCstr' k
  where
    resolveCheckCstr' (CheckAssertion c) = checkAssertion l c

ioCstrResult :: (Hashable a,IsScVar a,MonadIO m,Location loc) => loc -> IOCstr -> Proxy a -> TcM m (Maybe a)
ioCstrResult l iok proxy = do
    st <- liftIO $ readUniqRef (kStatus iok)
    case st of
        Evaluated t -> liftM Just $ cstrResult l (kCstr iok) proxy t
        Erroneous err -> return Nothing
        Unevaluated -> return Nothing
    where
    cstrResult :: (Hashable a,IsScVar a,Monad m,Location loc) => loc -> TCstr -> Proxy a -> ShowOrdDyn -> TcM m a
    cstrResult l k (Proxy::Proxy t) dyn = case fromShowOrdDyn dyn of
        Nothing -> genError (locpos l) $ text "Wrong IOCstr output type" <+> text (show dyn) <+> text "::" <+> text (show $     applyShowOrdDyn Generics.typeOf dyn) <+> text "with type" <+> text (show $ Generics.typeOf (error "applyShowOrdDyn"::t)) <+> pp k
        Just x -> return x

tcProve :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict)
tcProve l msg m = do
    newDict l $ "tcProve " ++ msg
    x <- m
    solve l msg
    d <- liftM (head . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (x:xs) = xs

proveWith :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (Either SecrecError (a,TDict))
proveWith l msg proof = try `catchError` (return . Left)
    where
    try = liftM Right $ tcProve l msg proof

prove :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a
prove l msg m = do
    (a,dict) <- tcProve l msg m
    addHeadTDict l dict
    return a

-- * Solving constraints

multipleSubstitutions :: (ProverK loc m) => loc -> Type -> [(Maybe Type,[TCstr])] -> TcM m ()
multipleSubstitutions l v ss = do
    --liftIO $ putStrLn $ ppr l ++ " multiple substitutions " ++ ppr v ++ " = " ++ ppr (sepBy comma $ map (pp . fst) ss)
    ok <- matchAll l v ss []
    case ok of
        [] -> return ()
        errs -> tcError (locpos l) $ Halt $ MultipleTypeSubstitutions $ map pp errs

matchAll :: (ProverK loc m) => loc -> Type -> [(Maybe Type,[TCstr])] -> [SecrecError] -> TcM m [SecrecError]
matchAll l t [] errs = return errs
matchAll l t (x:xs) errs = catchError
    -- match and solve all remaining constraints
    (matchOne l (length xs > 0) t x >> return [])
    -- backtrack and try another match
    (\e -> matchAll l t xs $ errs++[e])

matchOne :: (ProverK loc m) => loc -> Bool -> Type -> (Maybe Type,[TCstr]) -> TcM m ()
matchOne l doSolve t1 (mbt,deps) = do
    --liftIO $ putStrLn $ ppr l ++ " trying to match " ++ ppr t1 ++ " = " ++ ppr mbt
    --dict <- liftM (head . tDict) State.get
    --ss <- ppConstraints (tCstrs dict)
    --liftIO $ putStrLn $ "matchOne [" ++ show ss ++ "\n]"
    (_,ks) <- tcWithCstrs l "matchOne" $ maybe (return ()) (tcCstrM_ l . Unifies t1) mbt
    withDependencies ks $ mapM_ (tCstrM_ l) deps
    -- solve all other dependencies
    solve l "matchOne"
    --when doSolve $ solveAll l "matchone"

--matchOne :: (ProverK loc m) => loc -> Type -> [(Type,[TcCstr])] -> TcM m (Maybe [Doc])
--matchOne l t1 [] = return $ Just []
--matchOne l t1 ((t,ks):ts) = do
--    ok <- tryUnifies l t1 t
--    case ok of
--        Nothing -> do
--            mapM_ (tcCstrM_ l) ks
--            --liftM conc $ mapM (\t -> tryNotUnifies l t1 t) $ map fst ts
--            return $ Nothing
--        Just err -> liftM (fmap (pp err:)) $ matchOne l t1 ts
-- where
--    conc [] = Nothing
--    conc (Left x:xs) = fmap (x:) (conc xs)
--    conc (Right x:xs) = fmap (pp x:) (conc xs)
        
tryCstr :: (ProverK loc m) => loc -> TcM m a -> TcM m (Either SecrecError a)
tryCstr l m = (liftM Right $ prove l "tryCstr" $ m) `catchError` (return . Left)

tryCstrBool :: (ProverK loc m) => loc -> TcM m a -> TcM m Bool
tryCstrBool l m = liftM (maybe False (const True)) $ tryCstrMaybe l m

tryCstrMaybe :: (ProverK loc m) => loc -> TcM m a -> TcM m (Maybe a)
tryCstrMaybe l m = do
    mb <- tryCstr l m
    case mb of
        Right x -> return $ Just x
        Left err -> if isHaltError err
            then throwError err
            else do
--                liftIO $ putStrLn $ "tryCstrMaybe " ++ ppr err
                return Nothing

-- can the second argument be given the first type?
isTyOf :: (ProverK loc m) => loc -> Type -> Type -> TcM m Bool
isTyOf l tt t = tryCstrBool l $ unifies l (tyOf t) tt

--tryNotUnifies :: (ProverK loc m) => loc -> Type -> Type -> TcM m (Either Doc SecrecError)
--tryNotUnifies l t1 t2 = (prove l True (unifies l t1 t2) >> return (Right err)) `catchError` handleErr
--    where
--    err = GenericError (locpos l) $ text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "should not unify."
--    ok = text "Types" <+> quotes (pp t1) <+> text "and" <+> quotes (pp t2) <+> text "unify."
--    handleErr e = if isHaltError e
--        then throwError e
--        else return $ Left ok

-- checks if two types are equal, without using coercions, not performing substitutions
equals :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()
equals l (NoType _) (NoType _) = return ()
equals l (IdxT e1) (IdxT e2) = do
    equalsExpr l True e1 e2
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
equals l (VAType b1 sz1) (VAType b2 sz2) = do
    tcCstrM_ l $ Equals b1 b2
    equalsExprTy l True sz1 sz2
equals l (SType k1) (SType k2) | k1 == k2 = return ()
equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
equals l (CondType t1 c1) (CondType t2 c2) = do
    equals l t1 t2
    equalsExprTy l False c1 c2
equals l (VArrayT a1) (VArrayT a2) = equalsArray l a1 a2
equals l t1 t2 = constraintError (EqualityException "type") l t1 pp t2 pp Nothing

equalsArray :: (ProverK loc m) => loc -> VArrayType -> VArrayType -> TcM m ()
equalsArray l (VAVal ts1 b1) (VAVal ts2 b2) = do
    equalsList l ts1 ts2
    tcCstrM_ l $ Equals b1 b2
equalsArray l (VAVar v1 b1 sz1) (VAVar v2 b2 sz2) | v1 == v2 = do
    tcCstrM_ l $ Equals b1 b2
    equalsExprTy l True sz1 sz2
equalsArray l t1 t2 = constraintError (EqualityException "array") l t1 pp t2 pp Nothing

equalsSys :: (ProverK loc m) => loc -> SysType -> SysType -> TcM m ()
equalsSys l (SysPush t1) (SysPush t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysRet t1) (SysRet t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysRef t1) (SysRef t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l (SysCRef t1) (SysCRef t2) = tcCstrM_ l $ Equals t1 t2
equalsSys l t1 t2 = constraintError (EqualityException "syscall type") l t1 pp t2 pp Nothing

equalsSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()
equalsSec l Public Public = return ()
equalsSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
equalsSec l (SVar v1 k1) (SVar v2 k2) | v1 == v2 && k1 == k2 = return ()
equalsSec l (SVar v _) s2 = do
    s1 <- resolveSVar l v
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 (SVar v _) = do
    s2 <- resolveSVar l v
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 s2 = constraintError (EqualityException "security type") l s1 pp s2 pp Nothing

equalsDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m ()
equalsDec l (DVar v1) (DVar v2) | v1 == v2 = return ()
equalsDec l (DVar v1) d2 = do
    d1 <- resolveDVar l v1
    tcCstrM_ l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 (DVar v2) = do
    d2 <- resolveDVar l v2
    tcCstrM_ l $ Equals (DecT d1) (DecT d2)
equalsDec l d1 d2 | isJust (decTypeTyVarId d1) && decTypeTyVarId d1 == decTypeTyVarId d2 = return ()
equalsDec l d1 d2 = constraintError (EqualityException ("declaration type " ++ ppr (decTypeTyVarId d1) ++ " " ++ ppr (decTypeTyVarId d2) )) l d1 pp d2 pp Nothing

equalsComplex :: (ProverK loc m) => loc -> ComplexType -> ComplexType -> TcM m ()
--equalsComplex l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
--equalsComplex l (ArrayLit es1) (ArrayLit es2) = do
--    constraintList (EqualityException "size") (equalsExprTy l) l es1 es2
--    return ()
equalsComplex l (CType s1 t1 d1) (CType s2 t2 d2) = do
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
    equalsExprTy l True d1 d2
equalsComplex l (CVar v1) (CVar v2) | v1 == v2 = return ()
equalsComplex l (CVar v) c2 = do
    c1 <- resolveCVar l v
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l c1 (CVar v) = do
    c2 <- resolveCVar l v
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l Void Void = return ()
equalsComplex l c1 c2 = constraintError (EqualityException "complex type") l c1 pp c2 pp Nothing

equalsBase :: (ProverK loc m) => loc -> BaseType -> BaseType -> TcM m ()
equalsBase l (BVar v1) (BVar v2) | v1 == v2 = return ()
equalsBase l (BVar v) t2 = do
    t1 <- resolveBVar l v
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l t1 (BVar v) = do
    t2 <- resolveBVar l v
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l (TApp n1 ts1 d1) (TApp n2 ts2 d2) = do
    equalsTIdentifier l (Left n1) (Left n2)
    equalsTpltArgs l ts1 ts2
    equalsDec l d1 d2
equalsBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
equalsBase l b1 b2 = constraintError (EqualityException "base type") l b1 pp b2 pp Nothing

equalsFoldable :: (ProverK loc m,Foldable t) => loc -> t Type -> t Type -> TcM m ()
equalsFoldable l xs ys = equalsList l (toList xs) (toList ys)

equalsList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()
equalsList l [] [] = return ()
equalsList l (x:xs) (y:ys) = do
    tcCstrM_ l $ Equals x y
    equalsList l xs ys
equalsList l xs ys = constraintError (EqualityException "type") l xs pp ys pp Nothing

equalsPrim :: (ProverK loc m) => loc -> PrimitiveDatatype () -> PrimitiveDatatype () -> TcM m ()
equalsPrim l p1 p2 | p1 == p2 = return ()
equalsPrim l t1 t2 = constraintError (EqualityException "primitive type") l t1 pp t2 pp Nothing

expandCTypeVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m ComplexType
expandCTypeVar l v = do
    d <- newDomainTyVar AnyKind Nothing
    t <- newBaseTyVar Nothing
    dim <- newDimVar Nothing
    let ct = CType d t dim 
    addSubstM l True NoFailS (VarName TType v) $ ComplexT ct
    return ct

coerces2Type :: ProverK loc m => loc -> Type -> Type -> TcM m Type
coerces2Type l t1 t2 = do
    e1 <- liftM varExpr $ newTypedVar "e1" t1 Nothing
    e2 <- liftM varExpr $ newTypedVar "e2" t2 Nothing
    t3 <- newTyVar Nothing
    x1 <- newTypedVar "x1" t3 $ Just $ pp e1
    x2 <- newTypedVar "x2" t3 $ Just $ pp e2
    coerces2 l e1 e2 x1 x2
    return t3
    
assignExpr :: ProverK loc m => loc -> Var -> Expr -> TcM m ()
assignExpr l v e = tcCstrM_ l $ Unifies (IdxT $ varExpr v) (IdxT $ tokenizeExpr e)
    
tokenizeExpr :: Expr -> Expr
tokenizeExpr e = everywhereBut (mkQ False q) (mkT f) e
    where
    q :: Type -> Bool
    q t = True
    f :: VarIdentifier -> VarIdentifier
    f n = n { varIdTok = True }
    
coercesNType :: ProverK loc m => loc -> [Type] -> TcM m Type
coercesNType l [] = genTcError (locpos l) $ text "no types to coerce"
coercesNType l ts = foldr1M (coerces2Type l) ts

-- | Non-directed coercion, with implicit security coercions.
-- Returns the unified type.
-- applies substitutions
coerces2 :: (ProverK loc m) => loc -> Expr -> Expr -> Var -> Var -> TcM m ()
coerces2 l e1@(loc -> BaseT t1) e2@(loc -> BaseT t2) x1 x2 = do
    tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
    unifiesExprTy l True (varExpr x1) e1
    unifiesExprTy l True (varExpr x2) e2
coerces2 l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT t2) x1 x2 = coerces2Complex l e1 e2 x1 x2
coerces2 l e1@(loc -> ComplexT c1) e2@(loc -> BaseT b2) x1 x2 = do
    coerces2Complex l e1 (updLoc e2 $ ComplexT $ defCType b2) x1 x2
coerces2 l e1@(loc -> BaseT b1) e2@(loc -> ComplexT c2) x1 x2 =
    coerces2Complex l (updLoc e1 $ ComplexT $ defCType b1) e2 x1 x2
coerces2 l e1 e2 x1 x2 = addErrorM l (TypecheckerError (locpos l) . BiCoercionException "type" Nothing (ppExprTy e1) (ppExprTy e2) . Just) $ do
    tcCstrM_ l $ Unifies (loc e1) (loc e2)
    unifiesExprTy l True (varExpr x1) e1
    unifiesExprTy l True (varExpr x2) e2

coerces2Complex :: (ProverK loc m) => loc -> Expr -> Expr -> Var -> Var -> TcM m ()
coerces2Complex l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT t2) x1 x2 | isVoid t1 || isVoid t2 = addErrorM l (TypecheckerError (locpos l) . BiCoercionException "complex type" Nothing (ppExprTy e1) (ppExprTy e2) . Just) $ do
    tcCstrM_ l $ Unifies (ComplexT t1) (ComplexT t2)
    unifiesExprTy l True (varExpr x1) e1
    unifiesExprTy l True (varExpr x2) e2
coerces2Complex l e1@(loc -> ComplexT ct1@(CType s1 t1 d1)) e2@(loc -> ComplexT ct2@(CType s2 t2 d2)) x1 x2 = addErrorM l (TypecheckerError (locpos l) . (BiCoercionException "complex type") Nothing (ppExprTy e1) (ppExprTy e2) . Just) $ do
        tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
        tcCstrM_ l $ Coerces2SecDimSizes e1 e2 x1 x2
coerces2Complex l e1@(loc -> ComplexT t1@(CVar v1)) e2@(loc -> ComplexT t2@(CVar v2)) x1 x2 = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just t1',Just t2') -> tcCstrM_ l $ Coerces2 (updLoc e1 $ ComplexT t1') (updLoc e2 $ ComplexT t2') x1 x2
        (Just t1',Nothing) -> tcCstrM_ l $ Coerces2 (updLoc e1 $ ComplexT t1') e2 x1 x2
        (Nothing,Just t2') -> tcCstrM_ l $ Coerces2 e1 (updLoc e2 $ ComplexT t2') x1 x2
        (Nothing,Nothing) -> constraintError (\x y err -> Halt $ BiCoercionException "complex type" Nothing x y err) l e1 ppExprTy e2 ppExprTy Nothing
coerces2Complex l e1@(loc -> ComplexT t1@(CVar v)) e2@(loc -> ComplexT t2) x1 x2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t1' -> do
            tcCstrM_ l $ Coerces2 (updLoc e1 $ ComplexT t1') e2 x1 x2
        Nothing -> do
            t1' <- expandCTypeVar l v
            tcCstrM_ l $ Coerces2 (updLoc e1 $ ComplexT t1') e2 x1 x2
coerces2Complex l e1@(loc -> ComplexT t1) e2@(loc -> ComplexT t2@(CVar v)) x1 x2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t2' -> do
            tcCstrM_ l $ Coerces2 e1 (updLoc e2 $ ComplexT t2') x1 x2
        Nothing -> do
            t2' <- expandCTypeVar l v
            tcCstrM_ l $ Coerces2 e1 (updLoc e2 $ ComplexT t2') x1 x2
coerces2Complex l e1 e2 x1 x2 = constraintError (BiCoercionException "complex type" Nothing) l e1 ppExprTy e2 ppExprTy Nothing

coerces2SecDimSizes :: (ProverK loc m) => loc -> Expr -> Expr -> Var -> Var -> TcM m ()
coerces2SecDimSizes l e1@(loc -> ComplexT ct1@(CType s1 b1 d1)) e2@(loc -> ComplexT ct2@(CType s2 b2 d2)) x1 x2 = do
    tcCstrM_ l $ Unifies (BaseT b1) (BaseT b2)
    sord <- comparesSec l s1 s2
    let s3 = case compOrdering sord of { LT -> s2; otherwise -> s1 }
    dord <- comparesDim l d1 d2
    let d3 = case compOrdering dord of { LT -> d2; otherwise -> d1 } 
    let t3 = ComplexT $ CType s3 b1 d3
    tcCstrM_ l $ Unifies (loc x1) t3
    tcCstrM_ l $ Unifies (loc x2) t3
    coercesSecDimSizes l e1 x1
    coercesSecDimSizes l e2 x2
    
--coerces2Sec l e1@(loc -> ComplexT ct1) e2@(loc -> ComplexT ct2) x1 x2 = do
--    s1 <- cSecM l ct1
--    s2 <- cSecM l ct2
--    opts <- TcM $ lift Reader.ask
--    if implicitCoercions opts
--        then do
--            let left = prove l "coerces2Sec left" $ do
--                (_,ks) <- tcWithCstrs l "coerces2Sec left" $ tcCstrM_ l $ Unifies (loc x1) (ComplexT $ setCSec ct1 s2)
--                withDependencies ks $ do
--                    tcCstrM_ l $ CoercesSec e1 x1
--                    unifiesExprTy l (varExpr x2) e2
--            let right = prove l "coerces2Sec right" $ do
--                (_,ks) <- tcWithCstrs l "coerces2Sec right" $ tcCstrM_ l $ Unifies (loc x2) (ComplexT $ setCSec ct2 s1)
--                withDependencies ks $ do
--                    tcCstrM_ l $ CoercesSec e2 x2
--                    unifiesExprTy l (varExpr x1) e1
--            addErrorM l
--                (TypecheckerError (locpos l) . BiCoercionException "security type" Nothing (ppExprTy e1) (ppExprTy e2) . Just)
--                (left `mplus` right)
--        else do
--            tcCstrM_ l $ Unifies (ComplexT ct1) (ComplexT ct2)
--            unifiesExprTy l (varExpr x1) e1
--            unifiesExprTy l (varExpr x2) e2

coercesE :: (ProverK loc m) => loc -> Expr -> Type -> TcM m Expr
coercesE l e1 t2 = do
    x2 <- newTypedVar "coerces" t2 $ Just $ pp e1
    tcCstrM_ l $ Coerces e1 x2
    return $ varExpr x2

-- | Directed coercion, with implicit security type coercions and literal coercions
-- applies substitutions
-- returns a classify declaration
coerces :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coerces l e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(BaseT b2)) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "base type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    unifiesExprTy l True (varExpr x2) e1
coerces l e1@(loc -> t1@(ComplexT ct1)) x2@(loc -> t2@(ComplexT ct2)) = coercesComplex l e1 x2
coerces l e1@(loc -> t1@(ComplexT c1)) x2@(loc -> t2@(BaseT b2)) = coercesComplex l e1 (updLoc x2 $ ComplexT $ defCType b2)
coerces l e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(ComplexT c2)) = coercesComplex l (updLoc e1 $ ComplexT $ defCType b1) x2
coerces l e1 x2 = addErrorM l (TypecheckerError (locpos l) . (CoercionException "type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    unifiesExprTy l True (varExpr x2) e1

coercesComplexE :: (ProverK loc m) => loc -> Expr -> ComplexType -> TcM m Expr
coercesComplexE l e1 ct2 = do
    x2 <- newTypedVar "coerces_complex" (ComplexT ct2) $ Just $ pp e1
    coercesComplex l e1 x2
    return $ varExpr x2

coercesComplex :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesComplex l e1@(loc -> ComplexT t1) x2@(loc -> ComplexT t2) | isVoid t1 || isVoid t2 = addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") (ppExprTy e1) (ppExprTy x2) . Just) $ do
    unifiesExprTy l True (varExpr x2) e1
coercesComplex l e1@(loc -> ComplexT ct1@(CType s1 t1 d1)) x2@(loc -> ComplexT ct2@(CType s2 t2 d2)) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
        tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
        tcCstrM_ l $ CoercesSecDimSizes e1 x2
coercesComplex l e1@(loc -> ComplexT ct1@(CVar v1)) x2@(loc -> ComplexT ct2@(CVar v2)) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just ct1',Just ct2') -> do
            tcCstrM_ l $ Coerces (updLoc e1 $ ComplexT ct1') (updLoc x2 $ ComplexT ct2')
        (Just ct1',Nothing) -> do
            tcCstrM_ l $ Coerces (updLoc e1 $ ComplexT ct1') x2
        (Nothing,Just ct2') -> do
            tcCstrM_ l $ Coerces e1 (updLoc x2 $ ComplexT ct2')
        (Nothing,Nothing) -> constraintError (\x y err -> Halt $ CoercionException "complex type" x y err) l e1 ppExprTy x2 ppVarTy Nothing
coercesComplex l e1@(loc -> ComplexT (CVar v)) x2@(loc -> ComplexT ct2) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct1' -> coercesComplex l (updLoc e1 $ ComplexT ct1') x2
        Nothing -> do
            ct1' <- expandCTypeVar l v
            tcCstrM_ l $ Coerces (updLoc e1 $ ComplexT ct1') x2
coercesComplex l e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT (CVar v)) = do
    mb <- tryResolveCVar l v
    case mb of
        Just ct2' -> coercesComplex l e1 (updLoc x2 $ ComplexT ct2')
        Nothing -> do
            ct2' <- expandCTypeVar l v
            tcCstrM_ l $ Coerces e1 (updLoc x2 $ ComplexT ct2')
coercesComplex l e1 x2 = constraintError (CoercionException "complex type") l e1 ppExprTy x2 ppVarTy Nothing

cSec :: ComplexType -> Maybe SecType
cSec (CType s _ _) = Just s
cSec ct = Nothing

cSecM :: ProverK loc m => loc -> ComplexType -> TcM m SecType
cSecM l (CType s _ _) = return s
cSecM l (CVar v) = resolveCVar l v >>= cSecM l
cSecM l Void = genTcError (locpos l) $ text "no security type for void"

--coercesSecE :: (ProverK loc m) => loc -> Expr -> SecType -> TcM m Expr
--coercesSecE l e1 s2 = do
--    ct1 <- typeToComplexType l (loc e1)
--    let t2 = ComplexT $ setCSec ct1 s2
--    x2 <- newTypedVar "coerces_sec" t2 $ Just $ pp e1
--    coercesSec l e1 x2
--    return $ varExpr x2

coercesSecDimSizes :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesSecDimSizes l e1@(loc -> ComplexT (CVar v1)) x2 = do
    ct1 <- resolveCVar l v1
    coercesSecDimSizes l (updLoc e1 $ ComplexT ct1) x2
coercesSecDimSizes l e1 x2@(loc -> ComplexT (CVar v2)) = do
    ct2 <- resolveCVar l v2
    coercesSecDimSizes l e1 (updLoc x2 $ ComplexT ct2)
coercesSecDimSizes l e1@(loc -> ComplexT (CType s1 b1 d1)) x2@(loc -> ComplexT (CType s2 b2 d2)) = do
    let t3 = ComplexT $ CType s1 b2 d2 -- intermediate type
    x3 <- newTypedVar "e" t3 $ Just $ pp e1
    coercesDimSizes l e1 x3
    coercesSec l (varExpr x3) x2
coercesSecDimSizes l e1 x2 = constraintError (CoercionException "complex type security dimension") l e1 ppExprTy x2 ppVarTy Nothing

isZeroIdxExpr :: ProverK loc m => loc -> Expr -> TcM m ()
isZeroIdxExpr l e = do
    i <- evaluateIndexExpr l e
    case i of
        0 -> return ()
        otherwise -> genTcError (locpos l) $ text "non-zero index expression"

coercesDimSizes :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesDimSizes l e1@(loc -> ComplexT ct1@(CType s1 b1 d1)) x2@(loc -> ComplexT ct2@(CType s2 b2 d2)) = do
    opts <- askOpts
    mb1 <- tryError $ evaluateIndexExpr l d1
    mb2 <- tryError $ evaluateIndexExpr l d2
    case (mb1,mb2) of
        (_,Right 0) -> unifiesExprTy l True (varExpr x2) e1
        (Right ((>0) -> True),_) -> unifiesExprTy l True (varExpr x2) e1
        (Right 0,Right ((>0) -> True)) -> if implicitCoercions opts
            then do
                e2 <- repeatExpr l False e1 ct2
                unifiesExprTy l True (varExpr x2) e2
            else unifiesExprTy l True (varExpr x2) e1
        (Right 0,_) -> if implicitCoercions opts
            then do
                ks <- repeatsCstrs l e1 ct1 x2 d2
                isAnn <- getAnn
                isPure <- getPure
                tcCstrM_ l $ MultipleSubstitutions (IdxT d2) [
                    (Just (IdxT $ indexExpr 0),[TcK (Unifies (loc x2) (loc e1)) isAnn isPure,TcK (Unifies (IdxT $ varExpr x2) (IdxT e1)) isAnn isPure]),
                    (Nothing,TcK (NotEqual d2 (indexExpr 0)) isAnn isPure:ks)] 
            else unifiesExprTy l True (varExpr x2) e1
        (_,Right ((>0) -> True)) -> if implicitCoercions opts
            then do
                ks <- repeatsCstrs l e1 ct1 x2 d2
                isAnn <- getAnn
                isPure <- getPure
                tcCstrM_ l $ MultipleSubstitutions (IdxT d1) [
                    (Just (IdxT d2),[TcK (Unifies (loc x2) (loc e1)) isAnn isPure,TcK (Unifies (IdxT $ varExpr x2) (IdxT e1)) isAnn isPure]),
                    (Just (IdxT $ indexExpr 0),ks)]
            else unifiesExprTy l True (varExpr x2) e1
        otherwise -> addErrorM l (TypecheckerError (locpos l) . Halt . (CoercionException "complex type dimension") (ppExprTy e1) (ppVarTy x2) . Just) $ equalsExpr l True d1 d2
            
coercesDimSizes l e1 x2 = constraintError (CoercionException "complex type dimension") l e1 ppExprTy x2 ppVarTy Nothing

coercesSec :: (ProverK loc m) => loc -> Expr -> Var -> TcM m ()
coercesSec l e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT t2) = addErrorM l (TypecheckerError (locpos l) . (CoercionException "security type") (ppExprTy e1) (ppVarTy x2) . Just) $ do
    s2 <- cSecM l t2
    opts <- askOpts
    if implicitCoercions opts
        then do
            coercesSec' l e1 ct1 x2 s2
        else unifiesExprTy l True (varExpr x2) e1

coercesSec' :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> SecType -> TcM m ()
coercesSec' l e1 (cSec -> Just (SVar v1 k1)) x2 (SVar v2 k2) | v1 == v2 && k1 == k2 = do
    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 (cSec -> Just Public) x2 Public = do
    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just s1@Public) x2 s2@(SVar v AnyKind) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2' -> coercesSec' l e1 ct1 x2 s2'
        Nothing -> do
            opts <- askOpts
            if implicitCoercions opts
                then do
                    v' <- newDomainTyVar (PrivateKind Nothing) Nothing
                    ks <- classifiesCstrs l e1 ct1 x2 s2
                    isAnn <- getAnn
                    isPure <- getPure
                    tcCstrM_ l $ MultipleSubstitutions (SecT s2) [(Just (SecT Public),[TcK (Unifies (loc x2) (loc e1)) isAnn isPure,TcK (Unifies (IdxT $ varExpr x2) (IdxT e1)) isAnn isPure]),(Just (SecT v'),ks)]
                else do
                    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
                    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just Public) x2 s2@(SVar v k) = do
    s2' <- resolveSVar l v
    coercesSec' l e1 ct1 x2 s2'
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v _)) x2 s2@(Public) = do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just (Private d1 k1)) x2 (Private d2 k2) | d1 == d2 && k1 == k2 = do
    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just s1@(Private d1 k1)) x2 s2@(SVar v _) = do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v1 (PrivateKind k1))) x2 s2@(SVar v2 k2) = do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v1 AnyKind)) x2 s2@(Private d2 k2) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> do
            let ct1' = setCSec ct1 s1'
            coercesSec' l (updLoc e1 $ ComplexT ct1') ct1' x2 s2
        Nothing -> do
            opts <- askOpts
            if implicitCoercions opts
                then do
                    ks <- classifiesCstrs l e1 ct1 x2 s2
                    isAnn <- getAnn
                    isPure <- getPure
                    tcCstrM_ l $ MultipleSubstitutions (SecT s1) [(Just (SecT Public),ks),(Just (SecT s2),[TcK (Unifies (loc x2) (loc e1)) isAnn isPure,TcK (Unifies (IdxT $ varExpr x2) (IdxT e1)) isAnn isPure])]
                else do
                    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
                    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just s1@(SVar v _)) x2 s2@(Private d2 k2) = do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    unifiesExprTy l True (varExpr x2) e1
coercesSec' l e1 ct1@(cSec -> Just Public) x2 s2@(Private d2 k2) = do
    opts <- askOpts
    if implicitCoercions opts
        then do
            ks <- classifiesCstrs l e1 ct1 x2 s2
            forM_ ks $ tCstrM_ l
        else constraintError (CoercionException "security type") l e1 ppExprTy x2 ppVarTy Nothing
coercesSec' l e1 ct1@(cSec -> Just (SVar v1 _)) x2 s2@(SVar v2 _) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just t1',Just t2') -> coercesSec' l e1 (setCSec ct1 t1') x2 t2'
        (Just t1',Nothing) -> coercesSec' l e1 (setCSec ct1 t1') x2 s2
        (Nothing,Just t2') -> coercesSec' l e1 ct1 x2 t2'
        (Nothing,Nothing) -> constraintError (\x y -> Halt . CoercionException "security type" x y) l e1 ppExprTy x2 ppVarTy Nothing
coercesSec' l e1 t1 x2 t2 = constraintError (CoercionException "security type") l e1 ppExprTy x2 ppVarTy Nothing

classifiesCstrs :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> SecType -> TcM m [TCstr]
classifiesCstrs l e1 ct1 x2 s2 = do
    arr <- askErrorM''
    isAnn <- getAnn
    isPure <- getPure
    let ct2 = setCSec ct1 s2
    dec <- newDecVar Nothing
    let classify' = ProcedureName (DecT dec) $ mkVarId "classify"
    v1 <- newTypedVar "cl" (loc e1) $ Just $ pp e1
    let k1 = DelayedK (TcK (PDec (Left $ procedureNameId classify') Nothing [(e1,False)] (ComplexT ct2) dec False [v1]) isAnn isPure) arr
    let k2 = DelayedK (TcK (Unifies (loc x2) (ComplexT ct2)) isAnn isPure) arr
    let k3 = DelayedK (TcK (Unifies (IdxT $ varExpr x2) (IdxT $ ProcCallExpr (ComplexT ct2) classify' Nothing [(e1,False)])) isAnn isPure) arr
    return [k1,k2,k3]

repeatsCstrs :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> Expr -> TcM m [TCstr]
repeatsCstrs l e1 ct1 x2 d2 = do
    arr <- askErrorM''
    isAnn <- getAnn
    isPure <- getPure
    let ct2 = setCBase ct1 d2
    dec <- newDecVar Nothing
    let repeat' = ProcedureName (DecT dec) $ mkVarId "repeat"
    v1 <- newTypedVar "rp" (loc e1) $ Just $ pp e1
    let k1 = DelayedK (TcK (PDec (Left $ procedureNameId repeat') Nothing [(e1,False)] (ComplexT ct2) dec False [v1]) isAnn isPure) arr
    let k2 = DelayedK (TcK (Unifies (loc x2) (ComplexT ct2)) isAnn isPure) arr
    let k3 = DelayedK (TcK (Unifies (IdxT $ varExpr x2) (IdxT $ ProcCallExpr (ComplexT ct2) repeat' Nothing [(e1,False)])) isAnn isPure) arr
    return [k1,k2,k3]

coercesLit :: (ProverK loc m) => loc -> Expr -> TcM m ()
coercesLit l e@(LitPExpr t lit) = do
    b <- typeToBaseType l t
    coercesLitBase l (funit lit) b
coercesLit l (ArrayConstructorPExpr (ComplexT ct@(CType Public t d)) es) = do
    -- coerce the base types
    mapM_ (\e -> tcCstrM_ l $ Unifies (loc e) (BaseT t)) es
    -- match the dimension
    tcCstrM_ l $ Unifies (IdxT d) (IdxT $ indexExpr 1) -- dimension 1
coercesLit l e = constraintError (CoercionException "literal") l e pp (loc e) pp Nothing  

equalsLit :: (ProverK loc m) => loc -> Literal () -> Literal () -> TcM m ()
equalsLit l lit1 lit2 | lit1 == lit2 = return ()
equalsLit l (IntLit _ i1) (IntLit _ i2) | i1 == i2 = return ()
equalsLit l (IntLit _ i1) (FloatLit _ f2) | fromInteger i1 == f2 = return ()
equalsLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
equalsLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
equalsLit l lit1 lit2 = constraintError (EqualityException "literal type") l lit1 pp lit2 pp Nothing  

-- coerces a literal into a base type
coercesLitBase :: (ProverK loc m) => loc -> Literal () -> BaseType -> TcM m ()
coercesLitBase l lit t2@(BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
       Just t2' -> coercesLitBase l lit t2'
       Nothing -> do
           b <- case lit of
                StringLit _ s -> return $ TyPrim $ DatatypeString ()
                BoolLit _ b -> return $ TyPrim $ DatatypeBool ()
                otherwise -> constraintError (\x y e -> Halt $ CoercionException "literal base type" x y e) l lit pp t2 pp Nothing
           addSubstM l True CheckS (tyToVar $ BaseT t2) (BaseT b)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primIntBounds -> Just (min,max)))) = do
    unless (min <= i && i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLitBase l (IntLit _ i) (TyPrim (t@(primFloatBounds -> Just (min,max)))) = do
    unless (min <= fromInteger i && fromInteger i <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show i) (pp t) (show min) (show max)
coercesLitBase l (FloatLit _ f) (TyPrim (t@(primFloatBounds -> Just (min,max)))) | isPrimFloat t = do
    unless (min <= f && f <= max) $ tcWarn (locpos l) $ LiteralOutOfRange (show f) (pp t) (show min) (show max)
coercesLitBase l (BoolLit _ b) (TyPrim (DatatypeBool _)) = return ()
coercesLitBase l (StringLit _ s) (TyPrim (DatatypeString _)) = return ()
coercesLitBase l l1 t2 = constraintError (CoercionException "literal base type") l l1 pp t2 pp Nothing  

decToken :: MonadIO m => TcM m DecType
decToken = do
    i <- newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "tok" (Just mn) (Just i) True Nothing
    return $ DVar v

secToken :: MonadIO m => TcM m SecType
secToken = do
    i <- newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "tok" (Just mn) (Just i) True Nothing
    return $ SVar v AnyKind
    
baseToken :: MonadIO m => TcM m BaseType
baseToken = do
    i <- newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "tok" (Just mn) (Just i) True Nothing
    return $ BVar v

arrayToken :: MonadIO m => Type -> Expr -> TcM m VArrayType
arrayToken b sz = do
    i <- newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "tok" (Just mn) (Just i) True Nothing
    return $ VAVar v b sz

complexToken :: MonadIO m => TcM m ComplexType
complexToken = do
    i <- newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "tok" (Just mn) (Just i) True Nothing
    return $ CVar v

exprToken :: MonadIO m => TcM m Expr
exprToken = do
    i <- newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "tok" (Just mn) (Just i) True Nothing
    let t = BaseT $ BVar v
    return $ RVariablePExpr t (VarName t v)

-- | Checks if a type is more specific than another, performing substitutions
compares :: (ProverK loc m) => loc -> Type -> Type -> TcM m (Comparison (TcM m))
compares l (IdxT e1) (IdxT e2) = comparesExpr l True e1 e2
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
compares l (VArrayT a1) (VArrayT a2) = do
    comparesArray l a1 a2
compares l (VAType b1 sz1) (VAType b2 sz2) = do
    o1 <- compares l b1 b2
    o2 <- compares l (IdxT sz1) (IdxT sz2)
    appendComparisons l [o1,o2]
--compares l (CondType t1 c1) (CondType t2 c2) = do
--    o1 <- compares l t1 t2
--    o2 <- comparesCondExpression l c1 c2
--    return $ o1 `mappend` o2
--compares l (CondType t1 c1) t2 = do
--    o1 <- compares l t1 t2
--    o2 <- comparesCondExpression l c1 trueExpr
--    return $ o1 `mappend` o2
--compares l t1 (CondType t2 c2) = do
--    o1 <- compares l t1 t2
--    o2 <- comparesCondExpression l trueExpr c2
--    return $ o1 `mappend` o2
compares l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (ComparisonException "type") (pp t1) (pp t2) . Just)
    (equals l t1 t2 >> return (Comparison t1 t2 EQ))

comparesDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m (Comparison (TcM m))
comparesDec l t1@(DVar v1) t2@(DVar v2) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- decToken
            addSubstM l False CheckS (tyToVar $ DecT t1) $ DecT x
            addSubstM l False CheckS (tyToVar $ DecT t2) $ DecT x
            return (Comparison t1 t2 EQ)
        (Just t1',Nothing) -> comparesDec l t1' t2
        (Nothing,Just t2') -> comparesDec l t1 t2'
        (Just t1',Just t2') -> comparesDec l t1' t2'        
comparesDec l t1 t2@(DVar v) = do
    mb <- tryResolveDVar l v
    case mb of
        Just t2 -> comparesDec l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ DecT t2) $ DecT t1
            return (Comparison t1 t2 LT)
comparesDec l t1@(DVar v) t2 = do
    mb <- tryResolveDVar l v
    case mb of
        Just t1 -> comparesDec l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ DecT t1) $ DecT t2
            return (Comparison t1 t2 GT)
comparesDec l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (ComparisonException "declaration type") (pp t1) (pp t2) . Just)
    (equalsDec l t1 t2 >> return (Comparison t1 t2 EQ))

comparesArray :: (ProverK loc m) => loc -> VArrayType -> VArrayType -> TcM m (Comparison (TcM m))
comparesArray l a1@(VAVal ts1 _) a2@(VAVal ts2 _) = do
    comparesList l ts1 ts2
comparesArray l a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) | v1 == v2 = return (Comparison a1 a2 EQ)
comparesArray l a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) = do
    mb1 <- tryResolveVAVar l v1 sz1
    mb2 <- tryResolveVAVar l v2 sz2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- arrayToken b1 sz1
            addSubstM l False CheckS (tyToVar $ VArrayT a1) $ VArrayT x
            addSubstM l False CheckS (tyToVar $ VArrayT a2) $ VArrayT x
            return $ Comparison a1 a2 EQ
        (Just a1',Nothing) -> comparesArray l a1' a2
        (Nothing,Just a2') -> comparesArray l a1 a2'
        (Just a1',Just a2') -> comparesArray l a1' a2'        
comparesArray l a1 a2@(VAVar v2 b2 sz2) = do
    mb <- tryResolveVAVar l v2 sz2
    case mb of
        Just a2 -> comparesArray l a1 a2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ VArrayT a2) $ VArrayT a2
            return $ Comparison a1 a2 LT
comparesArray l a1@(VAVar v1 b1 sz1) a2 = do
    mb <- tryResolveVAVar l v1 sz1
    case mb of
        Just t1 -> comparesArray l a1 a2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ VArrayT a1) $ VArrayT a2
            return $ Comparison a1 a2 GT
--comparesArray l a1 a2 = constraintError (ComparisonException "array type") l a1 pp a2 pp Nothing

comparesSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m (Comparison (TcM m))
comparesSec l t1@Public t2@Public = return (Comparison t1 t2 EQ)
comparesSec l t1@(Private d1 k1) t2@(Private d2 k2) | d1 == d2 && k1 == k2 = return (Comparison t1 t2 EQ)
comparesSec l t1@Public t2@(Private {}) = return (Comparison t1 t2 LT) -- public computations are preferrable (because of coercions)
comparesSec l t1@(Private {}) t2@Public = return (Comparison t1 t2 GT) -- public computations are preferrable (because of coercions)
comparesSec l t1@(SVar v1 k1) t2@(SVar v2 k2) | v1 == v2 && k1 == k2 = return (Comparison t1 t2 EQ)
comparesSec l t1@(SVar v1 k1) t2@(SVar v2 k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> case (k1,k2) of
            (AnyKind,PrivateKind _) -> return $ Comparison t1 t2 GT
            (PrivateKind _,AnyKind) -> return $ Comparison t1 t2 LT
            (k1,(==k1) -> True) -> do
                x <- secToken
                addSubstM l False CheckS (tyToVar $ SecT t1) $ SecT x
                addSubstM l False CheckS (tyToVar $ SecT t2) $ SecT x
                return $ Comparison t1 t2 EQ
            otherwise -> constraintError (ComparisonException "security type") l t1 pp t2 pp Nothing
        (Just t1',Nothing) -> comparesSec l t1' t2
        (Nothing,Just t2') -> comparesSec l t1 t2'
        (Just t1',Just t2') -> comparesSec l t1' t2'        
comparesSec l t1 t2@(SVar v _) = do
    mb <- tryResolveSVar l v
    case mb of
        Just t2 -> comparesSec l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ SecT t2) $ SecT t1
            return $ Comparison t1 t2 LT
comparesSec l t1@(SVar v _) t2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just t1 -> comparesSec l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ SecT t1) $ SecT t2
            return $ Comparison t1 t2 GT
comparesSec l t1 t2 = constraintError (ComparisonException "security type") l t1 pp t2 pp Nothing

comparesSys :: (ProverK loc m) => loc -> SysType -> SysType -> TcM m (Comparison (TcM m))
comparesSys l (SysPush t1) (SysPush t2) = do
    compares l t1 t2
comparesSys l (SysRet t1) (SysRet t2) = do
    compares l t1 t2
comparesSys l (SysRef t1) (SysRef t2) = do
    compares l t1 t2
comparesSys l (SysCRef t1) (SysCRef t2) = do
    compares l t1 t2
comparesSys l t1 t2 = constraintError (ComparisonException "syscall type") l t1 pp t2 pp Nothing

comparesBase :: (ProverK loc m) => loc -> BaseType -> BaseType -> TcM m (Comparison (TcM m))
comparesBase l t1@(TApp n1 ts1 d1) t2@(TApp n2 ts2 d2) = do
    equalsTIdentifier l (Left n1) (Left n2)
    equalsTpltArgs l ts1 ts2
    equalsDec l d1 d2
    return (Comparison t1 t2 EQ)
comparesBase l t1@(TyPrim p1) t2@(TyPrim p2) = equalsPrim l p1 p2 >> return (Comparison t1 t2 EQ)
comparesBase l t1@(BVar v1) t2@(BVar v2) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- baseToken
            addSubstM l False CheckS (tyToVar $ BaseT t1) $ BaseT x
            addSubstM l False CheckS (tyToVar $ BaseT t2) $ BaseT x
            return $ Comparison t1 t2 EQ
        (Just t1',Nothing) -> comparesBase l t1' t2
        (Nothing,Just t2') -> comparesBase l t1 t2'
        (Just t1',Just t2') -> comparesBase l t1' t2'        
comparesBase l t1 t2@(BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> comparesBase l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ BaseT t2) $ BaseT t1
            return $ Comparison t1 t2 LT
comparesBase l t1@(BVar v) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> comparesBase l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ BaseT t1) $ BaseT t2
            return $ Comparison t1 t2 GT
comparesBase l t1 t2 = constraintError (ComparisonException "base type") l t1 pp t2 pp Nothing

comparesComplex :: (ProverK loc m) => loc -> ComplexType -> ComplexType -> TcM m (Comparison (TcM m))
comparesComplex l t1@Void t2@Void = return $ Comparison t1 t2 EQ
comparesComplex l ct1@(CType s1 t1 d1) ct2@(CType s2 t2 d2) = do -- we don't compare sizes
    o1 <- comparesSec l s1 s2
    o2 <- comparesBase l t1 t2
    o3 <- comparesDim l d1 d2
    appendComparisons l [o1,o2,o3]
comparesComplex l t1@(CVar v1) t2@(CVar v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Nothing,Nothing) -> do
            x <- complexToken
            addSubstM l False CheckS (tyToVar $ ComplexT t1) $ ComplexT x
            addSubstM l False CheckS (tyToVar $ ComplexT t2) $ ComplexT x
            return $ Comparison t1 t2 EQ
        (Just t1',Nothing) -> comparesComplex l t1' t2
        (Nothing,Just t2') -> comparesComplex l t1 t2'
        (Just t1',Just t2') -> comparesComplex l t1' t2'        
comparesComplex l t1 t2@(CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just t2 -> comparesComplex l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ ComplexT t2) $ ComplexT t1
            return $ Comparison t1 t2 LT
comparesComplex l t1@(CVar v) t2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just t1 -> comparesComplex l t1 t2
        Nothing -> do
            addSubstM l False CheckS (tyToVar $ ComplexT t1) $ ComplexT t2
            return $ Comparison t1 t2 GT
comparesComplex l t1 t2 = constraintError (ComparisonException "complex type") l t1 pp t2 pp Nothing
    
comparesFoldable :: (ProverK loc m,Foldable t) => loc -> t Type -> t Type -> TcM m (Comparison (TcM m))
comparesFoldable l xs ys = comparesList l (toList xs) (toList ys)

data Comparison m where
    Comparison :: VarsId m a => a -> a -> Ordering -> Comparison m
  deriving (Typeable)
    
instance Typeable m => Data (Comparison m) where
    gfoldl k z (Comparison x y o) = z Comparison `k` x `k` y `k` o
    gunfold k z c = error "gunfold Comparison"
    toConstr (Comparison {}) = con_Comparison
    dataTypeOf _ = ty_Comparison

con_Comparison = mkConstr ty_Comparison "Comparison" [] Prefix
ty_Comparison   = mkDataType "Language.SecreC.TypeChecker.Constraint.Comparison" [con_Comparison]
    
instance Eq (Comparison m) where
    (Comparison x1 y1 o1) == (Comparison x2 y2 o2) = o1 == o2
instance Ord (Comparison m) where
    compare (Comparison _ _ o1) (Comparison _ _ o2) = compare o1 o2
deriving instance Show (Comparison m)

instance PP (Comparison m) where
    pp (Comparison x y o) = pp x <+> pp o <+> pp y
instance (MonadIO m,GenVar VarIdentifier m,Typeable m) => Vars VarIdentifier m (Comparison m) where
    traverseVars f (Comparison x y o) = do
        x' <- f x
        y' <- f y
        o' <- f o
        return $ Comparison x' y' o'

compOrdering :: Comparison m -> Ordering
compOrdering (Comparison _ _ o) = o
ppCompares x y o = pp x <+> pp o <+> pp y

comparesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m (Comparison (TcM m))
comparesList l a@[] b@[] = return $ Comparison a b EQ
comparesList l a@(x:xs) b@(y:ys) = do
    f <- compares l x y
    g <- comparesList l xs ys
    appendComparison l f g
comparesList l xs ys = constraintError (ComparisonException "type") l xs pp ys pp Nothing
    
appendComparison :: (ProverK loc m) => loc -> Comparison (TcM m) -> Comparison (TcM m) -> TcM m (Comparison (TcM m))
appendComparison l (Comparison x1 x2 EQ) y@(Comparison y1 y2 o) = return y
appendComparison l x@(Comparison x1 x2 o) (Comparison y1 y2 EQ) = return x
appendComparison l (Comparison x1 x2 LT) y@(Comparison y1 y2 LT) = return y
appendComparison l (Comparison x1 x2 GT) y@(Comparison y1 y2 GT) = return y
appendComparison l c1 c2 = constraintError (ComparisonException "comparison") l c1 pp c2 pp Nothing

appendComparisons :: (ProverK loc m) => loc -> [Comparison (TcM m)] -> TcM m (Comparison (TcM m))
appendComparisons l xs = foldr0M (Comparison () () EQ) (appendComparison l) xs

-- | Non-directed unification, without implicit security coercions.
-- applies substitutions
unifies :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()
unifies l (IdxT e1) (IdxT e2) = unifiesExpr l True e1 e2
unifies l (SecT s1) (SecT s2) = unifiesSec l s1 s2
unifies l (SysT s1) (SysT s2) = unifiesSys l s1 s2
unifies l (BaseT b1) (BaseT b2) = unifiesBase l b1 b2
unifies l (BaseT b1) (ComplexT c2) = unifiesComplex l (defCType b1) c2
unifies l (ComplexT c1) (BaseT b2) = unifiesComplex l c1 (defCType b2)
unifies l (ComplexT c1) (ComplexT c2) = unifiesComplex l c1 c2
unifies l (DecT d1) (DecT d2) = unifiesDec l d1 d2
unifies l (VArrayT a1) (VArrayT a2) = unifiesArray l a1 a2
unifies l (VAType b1 sz1) (VAType b2 sz2) = do
    tcCstrM_ l $ Unifies b1 b2
    unifiesExprTy l True sz1 sz2
unifies l t1@(CondType t1' c1) t2@(CondType t2' c2) = do
    unifies l t1' t2'
    unifiesCondExpression l c1 c2
unifies l t1@(CondType t1' c1) t2 = do
    unifies l t1' t2
    unifiesCondExpression l c1 trueExpr
unifies l t1 t2@(CondType t2' c2) = do
    unifies l t1 t2'
    unifiesCondExpression l trueExpr c2
unifies l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (UnificationException "type") (pp t1) (pp t2) . Just)
    (equals l t1 t2)

unifiesArray :: (ProverK loc m) => loc -> VArrayType -> VArrayType -> TcM m ()
unifiesArray l (VAVal ts1 b1) (VAVal ts2 b2) = do
    unifiesList l ts1 ts2
    tcCstrM_ l $ Unifies b1 b2
unifiesArray l a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) = do
    tcCstrM_ l $ Unifies b1 b2
    unifiesExprTy l True sz1 sz2
    mb1 <- tryResolveVAVar l v1 sz1
    mb2 <- tryResolveVAVar l v2 sz2
    case (mb1,mb2) of
        (Just a1',Just a2') -> tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2')
        (Just a1',Nothing) -> tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2)
        (Nothing,Just a2') -> tcCstrM_ l $ Unifies (VArrayT a1) (VArrayT a2')
        (Nothing,Nothing) -> addSubstM l True CheckS (VarName (VAType b1 sz1) v1) (VArrayT a2)
unifiesArray l a1@(VAVar v1 b1 sz1) a2 = do
    mb1 <- tryResolveVAVar l v1 sz1
    unifiesExprTy l True sz1 (vArraySize a2)
    case mb1 of
        Just a1' -> tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2)
        Nothing -> addSubstM l True CheckS (VarName (VAType b1 sz1) v1) (VArrayT a2)
unifiesArray l a1 a2@(VAVar v2 b2 sz2) = do
    mb2 <- tryResolveVAVar l v2 sz2
    unifiesExprTy l True (vArraySize a1) (vArraySize a2)
    case mb2 of
        Just a2' -> tcCstrM_ l $ Unifies (VArrayT a1) (VArrayT a2')
        Nothing -> addSubstM l True CheckS (VarName (VAType b2 sz2) v2) (VArrayT a1)
--unifiesArray l a1 a2 = addErrorM l
--    (TypecheckerError (locpos l) . (UnificationException "array") (pp a1) (pp a2) . Just)
--    (equalsArray l a1 a2)

unifiesDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m ()
unifiesDec l d1@(DVar v1) d2@(DVar v2) = do
    mb1 <- tryResolveDVar l v1
    mb2 <- tryResolveDVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (DecT d1') (DecT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (DecT d1') (DecT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (DecT d1) (DecT d2')
        (Nothing,Nothing) -> addSubstM l True CheckS (VarName DType v1) (DecT d2)
unifiesDec l d1@(DVar v1) d2 = do
    mb <- tryResolveDVar l v1
    case mb of
        Just d1' -> tcCstrM_ l $ Unifies (DecT d1') (DecT d2)
        Nothing -> addSubstM l True CheckS (VarName DType v1) (DecT d2)
unifiesDec l d1 (DVar v2) = do
    mb <- tryResolveDVar l v2
    case mb of
        Just d2' -> tcCstrM_ l $ Unifies (DecT d1) (DecT d2')
        Nothing -> addSubstM l True CheckS (VarName DType v2) (DecT d1)
unifiesDec l t1 t2 = addErrorM l
    (TypecheckerError (locpos l) . (UnificationException "declaration type") (pp t1) (pp t2) . Just)
    (equalsDec l t1 t2)

unifiesComplex :: (ProverK loc m) => loc -> ComplexType -> ComplexType -> TcM m ()
unifiesComplex l Void Void = return ()
unifiesComplex l ct1@(CType s1 t1 d1) ct2@(CType s2 t2 d2) = addErrorM l (TypecheckerError (locpos l) . (UnificationException "complex") (pp ct1) (pp ct2) . Just) $ do
    tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
    tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
    unifiesExprTy l True d1 d2
unifiesComplex l d1@(CVar v1) d2@(CVar v2) = do
    mb1 <- tryResolveCVar l v1
    mb2 <- tryResolveCVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (ComplexT d1') (ComplexT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (ComplexT d1') (ComplexT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (ComplexT d1) (ComplexT d2')
        (Nothing,Nothing) -> addSubstM l True CheckS (VarName TType v1) (ComplexT d2)
unifiesComplex l (CVar v) c2 = do
    mb <- tryResolveCVar l v
    case mb of
        Just c1 -> tcCstrM_ l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l True CheckS (VarName TType v) (ComplexT c2)
unifiesComplex l c1 (CVar v) = do
    mb <- tryResolveCVar l v
    case mb of
        Just c2 -> tcCstrM_ l $ Unifies (ComplexT c1) (ComplexT c2)
        Nothing -> addSubstM l True CheckS (VarName TType v) (ComplexT c1)
unifiesComplex l t1 t2 = constraintError (UnificationException "complex type") l t1 pp t2 pp Nothing

unifiesSVar :: (ProverK loc m) => loc -> VarIdentifier -> SVarKind -> SecType -> TcM m ()
unifiesSVar l v k@AnyKind s1 = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind Nothing) s1@(Private _ _) = addSVarSubstM l v s1
unifiesSVar l v k@(PrivateKind (Just n)) s1@(Private d ((==n) -> True)) = addSVarSubstM l v s1
unifiesSVar l v k s1@(SVar v1 k1) = do
    mb <- tryResolveSVar l v1
    case mb of
        Just s1' -> tcCstrM_ l $ Unifies (SecT $ SVar v k) (SecT s1')
        Nothing -> if k <= k1
            then addSVarSubstM l v s1
            else addSVarSubstM l v1 (SVar v k)
unifiesSVar l v k s = constraintError (UnificationException "security type") l (SVar v k) pp s pp Nothing

addSVarSubstM l v s = addSubstM l True CheckS (VarName (SType $ secTypeKind s) v) (SecT s)

unifiesSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()
unifiesSec l Public Public = return ()
unifiesSec l (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = return ()
unifiesSec l d1@(SVar v1 k1) d2@(SVar v2 k2) = do
    mb1 <- tryResolveSVar l v1
    mb2 <- tryResolveSVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (SecT d1') (SecT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (SecT d1') (SecT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (SecT d1) (SecT d2')
        (Nothing,Nothing) -> unifiesSVar l v1 k1 d2
unifiesSec l (SVar v k) s2 = do
    mb <- tryResolveSVar l v
    case mb of
        Just s1 -> tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s2
unifiesSec l s1 (SVar v k) = do
    mb <- tryResolveSVar l v
    case mb of
        Just s2 -> tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        Nothing -> unifiesSVar l v k s1
unifiesSec l t1 t2 = constraintError (UnificationException "security type") l t1 pp t2 pp Nothing

unifiesSys :: (ProverK loc m) => loc -> SysType -> SysType -> TcM m ()
unifiesSys l (SysPush t1) (SysPush t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRet t1) (SysRet t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRef t1) (SysRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysCRef t1) (SysCRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l t1 t2 = constraintError (UnificationException "syscall type") l t1 pp t2 pp Nothing

unifiesBase :: (ProverK loc m) => loc -> BaseType -> BaseType -> TcM m ()
unifiesBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
unifiesBase l d1@(BVar v1) d2@(BVar v2) = do
    mb1 <- tryResolveBVar l v1
    mb2 <- tryResolveBVar l v2
    case (mb1,mb2) of
        (Just d1',Just d2') -> tcCstrM_ l $ Unifies (BaseT d1') (BaseT d2')
        (Just d1',Nothing) -> tcCstrM_ l $ Unifies (BaseT d1') (BaseT d2)
        (Nothing,Just d2') -> tcCstrM_ l $ Unifies (BaseT d1) (BaseT d2')
        (Nothing,Nothing) -> addSubstM l True CheckS (VarName BType v1) (BaseT d2)
unifiesBase l (BVar v) t2 = do
    mb <- tryResolveBVar l v
    case mb of
        Just t1 -> tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l True CheckS (VarName BType v) (BaseT t2)
unifiesBase l t1 (BVar v) = do
    mb <- tryResolveBVar l v
    case mb of
        Just t2 -> tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
        Nothing -> addSubstM l True CheckS (VarName BType v) (BaseT t1)
unifiesBase l (TApp n1 ts1 d1) (TApp n2 ts2 d2) = do
    unifiesTIdentifier l (Left n1) (Left n2)
    unifiesTpltArgs l ts1 ts2
    equalsDec l d1 d2
unifiesBase l t1 t2 = constraintError (UnificationException "base type") l t1 pp t2 pp Nothing

unifiesTpltArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m ()
unifiesTpltArgs l ts1 ts2 = matchTpltArgs l UnificationException (\x y -> tcCstrM_ l $ Unifies x y) ts1 ts2

equalsTpltArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m ()
equalsTpltArgs l ts1 ts2 = matchTpltArgs l EqualityException (\x y -> tcCstrM_ l $ Equals x y) ts1 ts2

matchTpltArgs :: (ProverK loc m) => loc -> (String -> Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> (Type -> Type -> TcM m ()) -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m ()
matchTpltArgs l ex match ts1 ts2 = addErrorM l (TypecheckerError (locpos l) . (ex "template arguments") (pp ts1) (pp ts2) . Just) $ matchTpltArgs' ts1 ts2
    where
    matchTpltArgs' ts1@(all (not . snd) -> True) [(t2,True)] = do
        let tt = tyOf t2
        b <- typeBase l tt
        match t2 (VArrayT $ VAVal (map fst ts1) b)
    matchTpltArgs' [(t1,True)] ts2@(all (not . snd) -> True) = do
        let tt = tyOf t1
        b <- typeBase l tt
        match t1 (VArrayT $ VAVal (map fst ts2) b)
    matchTpltArgs' [(t1,True)] [(t2,True)] = do
        match t1 t2
    matchTpltArgs' ts1 ts2 = do
        ts1' <- concatMapM (expandVariadicType l) ts1
        ts2' <- concatMapM (expandVariadicType l) ts2
        constraintList (ex "template arguments") match l ts1' ts2'
        return ()

equalsSizes :: (ProverK loc m) => loc -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
equalsSizes l szs1 szs2 = matchSizes l EqualityException (equalsExprTy l False) szs1 szs2

unifiesSizes :: (ProverK loc m) => loc -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
unifiesSizes l szs1 szs2 = matchSizes l UnificationException (unifiesExprTy l False) szs1 szs2

matchSizes :: (ProverK loc m) => loc -> (String -> Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> (Expr -> Expr -> TcM m ()) -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
matchSizes l ex match szs1 szs2 = addErrorM l (TypecheckerError (locpos l) . (ex "sizes") (ppOpt szs1 pp) (ppOpt szs2 pp) . Just) $ matchSizes' szs1 szs2
    where
    matchSizes' (Just szs1@(all (not . snd) -> True)) (Just [(e2,True)]) = do
        match e2 (ArrayConstructorPExpr (loc e2) $ map fst szs1)
    matchSizes' (Just [(e1,True)]) (Just szs2@(all (not . snd) -> True)) = do
        match e1 (ArrayConstructorPExpr (loc e1) $ map fst szs2)
    matchSizes' (Just [(e1,True)]) (Just [(e2,True)]) = do
        match e1 e2
    matchSizes' (Just szs1) (Just szs2) = do
        szs1' <- concatMapM (expandVariadicExpr l) szs1
        szs2' <- concatMapM (expandVariadicExpr l) szs2
        constraintList (ex "sizes") match l szs1' szs2'
        return ()
    matchSizes' sz1 sz2 = return () -- ignore if both sizes are not known

expandVariadicExpr :: (ProverK loc m) => loc -> (Expr,IsVariadic) -> TcM m [Expr]
expandVariadicExpr l (e,False) = case loc e of
    VAType {} -> genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (pp e)
    VArrayT {} -> genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (pp e)
    otherwise -> return [e]
expandVariadicExpr l (ArrayConstructorPExpr t es,True) = case t of
    VAType {} -> return es
    VArrayT {} -> return es
    otherwise -> genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)
expandVariadicExpr l (e,True) = do
    let t = loc e
    case t of
        VAType {} -> do
            d <- evaluateIndexExpr l =<< typeDim l t
            case d of
                0 -> return [e]
                1 -> do
                    sz <- evaluateIndexExpr l =<< typeSize l t
                    b <- typeBase l t
                    vs <- forM [0..pred (fromEnum sz)] $ \i -> newTypedVar ("vex"++show i) b Nothing
                    let es = map varExpr vs
                    tcCstrM_ l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t es)
                    return es
                otherwise -> genTcError (locpos l) $ text "Variadic matrix" <+> quotes (pp t) <+> text "not supported"
        VArrayT a -> do
            ts <- expandVariadicType l (VArrayT a,True)
            vs <- forM ts $ \t -> newTypedVar "vex" t Nothing
            let es = map varExpr vs
            tcCstrM_ l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t es)
            return es
        otherwise -> genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)
    
expandVariadicType :: (ProverK loc m) => loc -> (Type,IsVariadic) -> TcM m [Type]
expandVariadicType l (t,False) = case tyOf t of
    VAType {} -> genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (pp t)
    otherwise -> return [t]
expandVariadicType l (VArrayT (VAVal ts _),True) = return ts
expandVariadicType l (t@(VArrayT a),True) = do
    let tt = tyOf t
    sz <- evaluateIndexExpr l =<< typeSize l tt
    b <- typeBase l tt
    vs <- forM [0..pred (fromEnum sz)] $ \i -> newVarOf ("varr"++show i) b Nothing
    tcCstrM_ l $ Unifies t (VArrayT $ VAVal vs b)
    return vs
expandVariadicType l (t,True) = genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (pp t)

unifiesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    tcCstrM_ l $ Unifies x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError (UnificationException "type") l xs pp ys pp Nothing

resolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m ComplexType
resolveCVar l v = resolveTVar l v >>= typeToComplexType l

resolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m SecType
resolveSVar l v = resolveTVar l v >>= typeToSecType l

resolveVAVar :: (ProverK loc m) => loc -> VarIdentifier -> Expr -> TcM m VArrayType
resolveVAVar l v sz = resolveTVar l v >>= \t -> typeToVArrayType l t sz

resolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m DecType
resolveDVar l v = resolveTVar l v >>= typeToDecType l

resolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m BaseType
resolveBVar l v = resolveTVar l v >>= typeToBaseType l

resolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> do
            tcError (locpos l) $ Halt $ UnresolvedVariable (pp v)
        Just t -> return t

tryResolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe SecType)
tryResolveSVar l v = tryResolveTVar l v >>= mapM (typeToSecType l)

tryResolveVAVar :: (ProverK loc m) => loc -> VarIdentifier -> Expr -> TcM m (Maybe VArrayType)
tryResolveVAVar l v sz = tryResolveTVar l v >>= mapM (\t -> typeToVArrayType l t sz)

tryResolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe BaseType)
tryResolveBVar l v = tryResolveTVar l v >>= mapM (typeToBaseType l)

tryResolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe ComplexType)
tryResolveCVar l v = tryResolveTVar l v >>= mapM (typeToComplexType l)

tryResolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe DecType)
tryResolveDVar l v = tryResolveTVar l v >>= mapM (typeToDecType l)

-- | tries to resolve a type variable by looking its value in the substitutions and in the environment
tryResolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe Type)
tryResolveTVar l v | varIdTok v = return Nothing
tryResolveTVar l v = do
--    liftIO $ putStrLn $ "resolvingTVar " ++ ppr v
    addGDependencies $ Left v
    -- lookup in the substitution environment
    s <- getTSubsts l
    mb <- substsFromMap (unTSubsts s) v
    return $ mb

-- | tries to resolve an expression
tryResolveEVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> TcM m (Maybe (Expression VarIdentifier (Typed loc)))
tryResolveEVar l v t | varIdTok v = return Nothing
tryResolveEVar l v t = do
--    liftIO $ putStrLn $ "resolvingEVar " ++ ppr v
    addGDependencies $ Left v
    ss <- getTSubsts l
    case Map.lookup v (unTSubsts ss) of
        Just (IdxT e) -> do
            tcCstrM_ l $ Unifies t (loc e)
            return $ Just (fmap (Typed l) e)
        Just a@(VArrayT (VAVal (unIdxs -> Just es) _)) -> do
            tcCstrM_ l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ ArrayConstructorPExpr (tyOf a) es
        Just a@(VArrayT (VAVar v _ _)) -> do
            tcCstrM_ l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ RVariablePExpr (tyOf a) (VarName (tyOf a) v)
        otherwise -> return Nothing

unIdx :: Type -> Maybe Expr
unIdx (IdxT e) = Just e
unIdx _ = Nothing

unIdxs :: [Type] -> Maybe [Expr]
unIdxs [] = Just []
unIdxs (x:xs) = case (unIdx x,unIdxs xs) of
    (Just x,Just xs) -> Just (x:xs)
    otherwise -> Nothing

setCSec (CType _ t d) s = CType s t d
setCBase (CType s t _) d = CType s t d

isSupportedPrint :: (ProverK loc m) => loc -> [(Expr,IsVariadic)] -> [Var] -> TcM m ()
isSupportedPrint l es xs = forM_ (zip es xs) $ \(e,x) -> do
    (dec,[(y,_)]) <- pDecCstrM l False True (Left $ mkVarId "tostring") Nothing [e] (BaseT string)
    unifiesExprTy l True (varExpr x) y
    return ()

unifiesCondExpression :: (ProverK loc m) => loc -> Cond -> Cond -> TcM m ()
unifiesCondExpression l e1 e2 = unifiesExprTy l False e1 e2 `mplus` satisfiesCondExpressions l [e1,e2]

satisfiesCondExpressions :: (ProverK loc m) => loc -> [Cond] -> TcM m ()
satisfiesCondExpressions l is = do
    cs <- prove l "satisfiesCondExpressions" $ mapM (expr2IExpr . fmap (Typed l)) is
    isValid l $ iAnd cs

unifiesExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
unifiesExpr l doStatic e1@(RVariablePExpr t1 v1@(VarName _ n)) e2@(RVariablePExpr t2 v2) = do
    mb1 <- tryResolveEVar l (varNameId v1) t1
    mb2 <- tryResolveEVar l (varNameId v2) t2
    case (mb1,mb2) of
        (Just e1',Just e2') -> unifiesExpr l doStatic (fmap typed e1') (fmap typed e2')
        (Just e1',Nothing) -> unifiesExpr l doStatic (fmap typed e1') e2
        (Nothing,Just e2') -> unifiesExpr l doStatic e1 (fmap typed e2')
        (Nothing,Nothing) -> addValueM True l v1 e2
unifiesExpr l doStatic e1@(RVariablePExpr t1 v1) e2 = do
    mb <- tryResolveEVar l (varNameId v1) t1
    case mb of
        Nothing -> addValueM True l v1 e2
        Just e1' -> unifiesExpr l doStatic (fmap typed e1') e2
unifiesExpr l doStatic e1 e2@(RVariablePExpr t2 v2) = do
    mb <- tryResolveEVar l (varNameId v2) t2
    case mb of
        Nothing -> addValueM True l v2 e1
        Just e2' -> unifiesExpr l doStatic e1 (fmap typed e2')
unifiesExpr l doStatic (ArrayConstructorPExpr t1 es1) (ArrayConstructorPExpr t2 es2) = do
    constraintList (UnificationException "expression") (unifiesExprTy l doStatic) l es1 es2
    return ()
unifiesExpr l doStatic e1 e2 = addErrorM l (TypecheckerError (locpos l) . (EqualityException "expression") (pp e1) (pp e2) . Just) $ equalsExpr l doStatic e1 e2

equalsTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()
equalsTIdentifier l (Right (Right (OpCast _ t1))) (Right (Right (OpCast _ t2))) = do
    equals l (castTypeToType t1) (castTypeToType t2)
equalsTIdentifier l (Right (Right op1)) (Right (Right op2)) | funit op1 == funit op2 = return ()
equalsTIdentifier l n1 n2 | n1 == n2 = return ()
equalsTIdentifier l t1 t2 = constraintError (UnificationException "identifier") l t1 pp t2 pp Nothing
    
unifiesTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()
unifiesTIdentifier l (Right (Right (OpCast _ t1))) (Right (Right (OpCast _ t2))) = do
    unifies l (castTypeToType t1) (castTypeToType t2)
unifiesTIdentifier l (Right (Right op1)) (Right (Right op2)) | funit op1 == funit op2 = return ()
unifiesTIdentifier l n1 n2 | n1 == n2 = return ()
unifiesTIdentifier l t1 t2 = constraintError (UnificationException "identifier") l t1 pp t2 pp Nothing

equalsExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
equalsExpr l doStatic e1 e2 | e1 == e2 = return ()
equalsExpr l doStatic (LitPExpr t1 lit1) (LitPExpr t2 lit2) = do
    equalsLit l (funit lit1) (funit lit2)
    tcCstrM_ l $ Unifies t1 t2
equalsExpr l True e1 e2 = do
    i1 <- prove l ("equalsExpr1 " ++ ppr e1) $ expr2IExpr $ fmap (Typed l) e1
    i2 <- prove l ("equalsExpr2 " ++ ppr e2) $ expr2IExpr $ fmap (Typed l) e2
    isValid l (IBinOp (IEq) i1 i2)
equalsExpr l False e1 e2 = do
    eq <- eqExprs l False e1 e2
    getDeps >>= \deps -> checkCstrM_ l deps $ CheckAssertion eq

comparesTpltArgs :: (Vars VarIdentifier (TcM m) [(Type, IsVariadic)],ProverK loc m)
    => loc -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m (Comparison (TcM m))
comparesTpltArgs l ts1 ts2 = do
    os <- constraintList (ComparisonException "template arguments") comparesTpltArg l ts1 ts2
    appendComparisons l os
  where
    comparesTpltArg (t1,b1) (t2,b2) = do
        unless (b1 == b2) $ genTcError (locpos l) $ text "incomparable template arguments"
        compares l t1 t2

comparesDim :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m (Comparison (TcM m))
comparesDim l e1 e2 = do
    z1 <- tryError $ equalsExpr l True e1 (indexExpr 0)
    z2 <- tryError $ equalsExpr l True e2 (indexExpr 0)
    case (z1,z2) of
        (Right _,Right _) -> return (Comparison e1 e2 EQ)
        (Right _,Left _) -> return (Comparison e1 e2 LT)
        (Left _,Right _) -> return (Comparison e1 e2 GT)
        otherwise -> comparesExpr l True e1 e2
    
comparesExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
comparesExpr l doStatic e1 e2 = addErrorM l (TypecheckerError (locpos l) . (ComparisonException "expression") (pp e1) (pp e2) . Just) (comparesExpr' l doStatic e1 e2)
    where
    comparesExpr' :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
    comparesExpr' l doStatic e1 e2 | e1 == e2 = return (Comparison e1 e2 EQ)
    comparesExpr' l doStatic e1@(RVariablePExpr t1 v1@(VarName _ n)) e2@(RVariablePExpr t2 v2) = do
        mb1 <- tryResolveEVar l (varNameId v1) t1
        mb2 <- tryResolveEVar l (varNameId v2) t2
        case (mb1,mb2) of
            (Nothing,Nothing) -> do
                x <- exprToken
                addValueM False l v1 x
                addValueM False l v2 x
                return (Comparison e1 e2 EQ)
            (Just e1',Nothing) -> comparesExpr' l doStatic (fmap typed e1') e2
            (Nothing,Just e2') -> comparesExpr' l doStatic e1 (fmap typed e2')
            (Just e1',Just e2') -> comparesExpr' l doStatic (fmap typed e1') (fmap typed e2')
    comparesExpr' l doStatic e1@(RVariablePExpr t1 v1) e2 = do
        mb <- tryResolveEVar l (varNameId v1) t1
        case mb of
            Nothing -> do
                addValueM False l v1 e2
                return (Comparison e1 e2 GT)
            Just e1' -> comparesExpr' l doStatic (fmap typed e1') e2
    comparesExpr' l doStatic e1 e2@(RVariablePExpr t2 v2) = do
        mb <- tryResolveEVar l (varNameId v2) t2
        case mb of
            Nothing -> do
                addValueM False l v2 e1
                return (Comparison e1 e2 LT)
            Just e2' -> comparesExpr' l doStatic e1 (fmap typed e2')
    comparesExpr' l doStatic e1 e2 = do
        equalsExpr l doStatic e1 e2 >> return (Comparison e1 e2 EQ)

equalsExprTy :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
equalsExprTy l doStatic e1 e2 = addErrorM l (TypecheckerError (locpos l) . (EqualityException "typed expression") (ppExprTy e1) (ppExprTy e2) . Just) $ do
    equalsExpr l doStatic e1 e2
    tcCstrM_ l $ Equals (loc e1) (loc e2)

unifiesExprTy :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m ()
unifiesExprTy l doStatic e1 e2 = addErrorM l (TypecheckerError (locpos l) . (UnificationException "typed expression") (ppExprTy e1) (ppExprTy e2) . Just) $ do
    tcCstrM_ l $ Unifies (loc e1) (loc e2)
    unifiesExpr l doStatic e1 e2
    
constraintError :: (ProverK loc m,VarsId (TcM m) a,VarsId (TcM m) b) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> Doc) -> b -> (b -> Doc) -> Maybe SecrecError -> TcM m res
constraintError k l e1 pp1 e2 pp2 (Just suberr) = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    tcError (locpos l) $ k (pp1 e1') (pp2 e2') $ Just suberr
constraintError k l e1 pp1 e2 pp2 Nothing = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    tcError (locpos l) $ k (pp1 e1') (pp2 e2') Nothing

constraintList :: (ProverK loc m,VarsId (TcM m) [a],VarsId (TcM m) [b]) =>
    (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr)
    -> (a -> b -> TcM m x) -> loc -> [a] -> [b] -> TcM m [x]
constraintList err f l [] [] = return []
constraintList err f l (x:xs) (y:ys) = do
    r <- f x y
    rs <- constraintList err f l xs ys
    return (r:rs)
constraintList err f l xs ys = constraintError err l xs pp ys pp Nothing

checkAssertion :: (ProverK loc m) => loc -> Expr -> TcM m ()
checkAssertion l e = do
    ic <- prove l "checkassertion" $ expr2IExpr $ fmap (Typed l) e
    isValid l ic
    
checkEqual :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()
checkEqual l e1 e2 = do
    (i1,i2) <- prove l "checkequal" $ do
        i1 <- expr2IExpr $ fmap (Typed l) e1
        i2 <- expr2IExpr $ fmap (Typed l) e2
        return (i1,i2)
    isValid l $ IBinOp (IEq) i1 i2

checkIndex :: (ProverK loc m,SMTK loc) => loc -> Expr -> TcM m ()
checkIndex l e = do
    ie <- prove l "checkindex" $ expr2IExpr $ fmap (Typed l) e
    isValid l $ IBinOp (ILeq) (ILit $ IUint64 0) ie

pDecCstrM :: (ProverK loc m) => loc -> Bool -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(Expr,IsVariadic)] -> Type -> TcM m (DecType,[(Expr,IsVariadic)])
pDecCstrM l isTop doCoerce pid targs es tret = do
    dec <- newDecVar Nothing
    opts <- askOpts
    let tck = if isTop then topTcCstrM_ else tcCstrM_
    if (doCoerce && implicitCoercions opts)
        then do
            xs <- forM es $ \e -> do
                tx <- newTyVar Nothing
                x <- newTypedVar "parg" tx $ Just $ ppVariadicArg pp e
                return x
            tck l $ PDec pid targs es tret dec True xs
            let es' = zip (map varExpr xs) (map snd es)
            return (dec,es')
        else do
            xs <- forM es $ \e -> do
                let tx = loc $ fst e
                x <- newTypedVar "parg" tx $ Just $ ppVariadicArg pp e
                return x
            tck l $ PDec pid targs es tret dec False xs
            return (dec,es)
