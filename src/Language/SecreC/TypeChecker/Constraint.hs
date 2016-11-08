{-# LANGUAGE DeriveGeneric, ScopedTypeVariables, FlexibleInstances, ConstraintKinds, StandaloneDeriving, DeriveDataTypeable, MultiParamTypeClasses, TupleSections, GADTs, FlexibleContexts, ViewPatterns #-}

module Language.SecreC.TypeChecker.Constraint where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Template
import {-# SOURCE #-} Language.SecreC.Prover.Expression
import {-# SOURCE #-} Language.SecreC.Transformation.Simplify
import Language.SecreC.Prover.Semantics
import Language.SecreC.Prover.SMT
import Language.SecreC.Prover.Base
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Pretty as PP
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
import Data.Map (Map(..))
import qualified Data.Generics as Generics
import Data.List as List
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.PatriciaTree as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.Graph.Inductive.Query.TransClos as Graph
import qualified Data.Graph.Inductive.Basic as Graph

import GHC.Generics (Generic)

import Text.PrettyPrint as PP hiding (equals)

import Safe

-- * Constraint Engine

-- solves all hypotheses in the environment
solveHypotheses :: (ProverK loc m) => loc -> TcM m [IExpr]
solveHypotheses l = do
    hyps <- liftM Set.toList getHyps
    (_,dhyps) <- tcWith (locpos l) "solveHypotheses" $ do
        addHeadTCstrs l "solveHypotheses" $ Graph.insNodes (map (\x -> (ioCstrId $ unLoc x,x)) hyps) Graph.empty
        solveTop l "solveHypotheses"
    addHeadTDict l "solveHypotheses" $ dhyps { tCstrs = Graph.empty }
    -- collect the result for the hypotheses
    liftM concat $ forM hyps $ \(Loc _ iok) -> do
        liftM (maybeToList . join) $ ioCstrResult l iok proxy
  where proxy = Proxy :: Proxy (Maybe IExpr)

solveSelectionWith :: ProverK loc m => loc -> String -> SolveMode -> Set LocIOCstr -> TcM m ()
solveSelectionWith l msg mode cs = tcNoDeps $ do
    newDict l $ "solveSelection " ++ msg
    mb <- solveMb l ("solveSelection " ++ msg ++ " " ++ show mode) mode cs
    case mb of
        Just err -> throwError err
        Nothing -> do
            d <- liftM (headNe . tDict) State.get
            State.modify $ \e -> e { tDict = dropDict (tDict e) }
            addHeadTDict l (msg++" solveSelectionWith") d
  where dropDict (ConsNe x xs) = xs

-- | solves the whole constraint stack
--solveAll :: ProverK loc m => loc -> String -> TcM m ()
--solveAll l msg = do
--    env <- State.get
--    let dicts = tDict env
--    let depth = length dicts
--    liftIO $ putStrLn $ "solveAll " ++ msg ++ " " ++ show depth ++ " " ++ ppr (vcat $ map (\x -> text ">" <> pp x) dicts)
--    replicateM_ depth $ do
--        solve' l msg True
--        env <- State.get
--        dicts' <- mergeHeadDict l (tDict env)
--        State.put $ env { tDict = dicts' }
--    State.modify $ \env -> env { tDict = (replicate (depth - 1) emptyTDict) ++ tDict env }

mergeHeadDict :: ProverK loc m => loc -> [TDict] -> TcM m [TDict]
mergeHeadDict l [] = return []
mergeHeadDict l [x] = return [x]
mergeHeadDict l (x:y:xs) = do
    xy <- appendTDict l (SubstMode NoCheckS False) x y
    return (xy:xs)

solveTop :: ProverK loc m => loc -> String -> TcM m ()
solveTop l msg = do
    mode <- defaultSolveMode
    solveWith l msg $ mkHaltFailMode $ mode { solveScope = SolveAll }
    gr <- State.gets (tCstrs . headNe . tDict)
    unless (Graph.isEmpty gr) $ do
        doc <- ppConstraints gr
        ppl <- ppr l
        error $ "solveTop: " ++ ppl ++ " " ++ msg ++ " couldn't solve all constraints " ++ show doc

solve :: ProverK loc m => loc -> String -> TcM m ()
solve l msg = do
    mode <- defaultSolveMode
    solveWith l msg mode

defaultSolveMode :: ProverK Position m => TcM m SolveMode
defaultSolveMode = do
    doAll <- getDoAll
    doSolve <- getDoSolve
    case (doAll,doSolve) of
        (True,True) -> return $ SolveMode (AllFail True) SolveAll
        (True,False) -> return $ SolveMode (AllFail False) SolveGlobal
        otherwise -> return $ SolveMode (AllFail False) SolveLocal
    
-- | solves all constraints in the top environment
solveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m ()
solveWith l msg mode = do
    cs <- topCstrs l
    mb <- solveMb l msg mode cs
    case mb of
        Nothing -> return ()
        Just err -> throwError err

solveMb :: (ProverK loc m) => loc -> String -> SolveMode -> Set LocIOCstr -> TcM m (Maybe SecrecError)
solveMb l msg mode cs = do
    --liftIO $ putStrLn $ "solving " ++ msg ++ " " ++ show doAll ++ " " ++ show doSolve ++ " " ++ ppr l ++ ppr cs
    if Set.null cs
        then return Nothing
        else newErrorM $ tcNoDeps $ do
            gr' <- buildCstrGraph l (mapSet (ioCstrId . unLoc) cs)
            debugTc $ do
                ppl <- ppr l
                ss <- ppConstraints gr'
                liftIO $ putStrLn $ "solveMb " ++ show msg ++ " " ++ ppl ++ " [" ++ show ss ++ "\n]"
            mb <- solveCstrs l msg mode
            --liftIO $ putStrLn $ "solved " ++ show msg ++ " " ++ ppr l
            --updateHeadTCstrs $ \d -> return ((),Graph.nfilter (`elem` Graph.nodes gr) d)
            debugTc $ do
                ppl <- ppr l
                ppmb <- ppr (isJust mb)
                liftIO $ putStrLn $ "solvedMb " ++ msg ++ " " ++ ppl ++ ppmb
            return mb

priorityRoots :: ProverK Position m => (x,LocIOCstr) -> (x,LocIOCstr) -> TcM m Ordering
priorityRoots x y = priorityTCstr (kCstr $ unLoc $ snd x) (kCstr $ unLoc $ snd y)

solveCstrs :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m (Maybe SecrecError)
solveCstrs l msg mode = do
    dicts <- liftM tDict State.get
    let dict = headNe dicts
    debugTc $ do
        ss <- ppConstraints (tCstrs dict)
        ppl <- ppr l
        liftIO $ putStrLn $ (concat $ replicate (length dicts) ">") ++ "solveCstrs " ++ show msg ++ " " ++ show mode ++ " " ++ ppl ++ " [" ++ show ss ++ "\n]"
        forM (tail $ Foldable.toList dicts) $ \d -> do
          ssd <- ppConstraints (tCstrs d)
          liftIO $ putStrLn $ "\n[" ++ show ssd ++ "\n]"
        doc <- ppTSubsts =<< getTSubsts l
        liftIO $ putStrLn $ show doc
        frees <- getFrees l
        ppfrees <- ppr frees
        liftIO $ putStrLn $ "frees: " ++ ppfrees
    gr <- liftM (tCstrs . headNe . tDict) State.get
    if (Graph.isEmpty gr)
        then do
            debugTc $ liftIO $ putStrLn $ "solvesCstrs " ++ msg ++ show mode ++ " empty "
            return Nothing
        else do
            roots <- sortByM priorityRoots $ rootsGr gr -- sort by constraint priority
            when (List.null roots) $ do
                ppl <- ppr l
                ppgr <- ppr gr
                ppedges <- mapM pp $ Graph.edges gr
                error $ "solveCstrs: no root constraints to proceed " ++ ppl ++ " " ++ ppgr ++ "\n\n" ++ show (sepBy comma ppedges)
            debugTc $ do
                pproots <- mapM (pp . ioCstrId . unLoc . snd) roots
                liftIO $ putStrLn $ "solveCstrsG " ++ msg ++ show mode ++ " [" ++ show (sepBy space pproots) ++ "\n]"
            go <- trySolveSomeCstrs mode $ map snd roots
            case go of
                -- no constraint left to solve
                Left False -> error $ "solveCstrs hiatus"
                -- at least one constraint solved
                Left True -> do
                    solveCstrs l msg mode
                -- no constraint solved because of errors
                Right errs -> do
                    mb <- solveErrors l mode errs
                    debugTc $ do
                        ppmb <- ppr mb
                        liftIO $ putStrLn $ "solvesCstrs " ++ msg ++ show mode ++ " exit " ++ ppmb
                    return mb

-- Left True = one constraint solved
-- Left False = no remaining unsolved constraints
-- Right err = failed
type SolveRes = Either Bool [(LocIOCstr,SecrecError)]

mergeSolveRes :: SolveRes -> SolveRes -> SolveRes
mergeSolveRes (Left True) b = Left True
mergeSolveRes (Left False) b = b
mergeSolveRes a (Left True) = Left True
mergeSolveRes a (Left False) = a
mergeSolveRes (Right a) (Right b) = Right (a ++ b)

isErrorSolveRes :: Bool -> SolveRes -> Bool
isErrorSolveRes haltFail (Left _) = False
isErrorSolveRes False (Right es) = any (not . isHaltError . snd) es
isErrorSolveRes True (Right es) = not $ null es

-- | tries to solve one or more constraints
trySolveSomeCstrs :: (ProverK Position m) => SolveMode -> [LocIOCstr] -> TcM m SolveRes
trySolveSomeCstrs mode = foldlM solveBound (Left False)
    where
    solveBound b x = case solveFail mode of
        FirstFail haltFail -> if isErrorSolveRes False b -- we don't fail on halting errors during constraint resolution
            then return b
            else find b x
        otherwise -> find b x
    find b x = do
        found <- findCstr x
        if found
            then do
                ok <- trySolveCstr mode x
                return (mergeSolveRes b ok)
            else do
                debugTc $ do
                    ppx <- ppr (ioCstrId $ unLoc x)
                    liftIO $ putStrLn $ "didn't find queued constraint " ++ ppx
                return b

-- since templates are only resolved at instantiation time, we prevent solving of overloadable constraints
trySolveCstr :: (ProverK Position m) => SolveMode -> LocIOCstr -> TcM m SolveRes
trySolveCstr mode (Loc l iok) = do
    isMul <- isMultipleSubstsCstr (kCstr iok)
    if solveScope mode < SolveAll && isMul
        then return $ Right [(Loc l iok,TypecheckerError (locpos l) $ Halt $ GenTcError (text "Unsolved multiple substitutions constraint") Nothing)]
        else do
            isGlobal <- isGlobalCstr (kCstr iok)
            if solveScope mode < SolveGlobal && isGlobal
                then return $ Right [(Loc l iok,TypecheckerError (locpos l) $ Halt $ GenTcError (text "Unsolved global constraint") Nothing)]
                else catchError
                    (do
                        opens <- getOpensSet
                        if Set.member (ioCstrId iok) opens
                            then do
                                debugTc $ do
                                    ppx <- ppr (ioCstrId iok)
                                    liftIO $ putStrLn $ "found opened or promoted constraint " ++ ppx
                                return (Left False)
                            else solveIOCstr_ l "trySolveCstr" mode iok >> return (Left True)
                    )
                    (\e -> return $ Right [(Loc l iok,e)])

findCstr :: Monad m => LocIOCstr -> TcM m Bool
findCstr x = do
    ks <- State.gets (flattenIOCstrGraphSet . tCstrs . headNe . tDict)
--    ks <- State.gets (mconcat . map (flattenIOCstrGraphSet . tCstrs) . tDict)
    return $ Set.member x ks

getErrors :: [(LocIOCstr,SecrecError)] -> [SecrecError]
getErrors = map snd . flattenErrors
    
flattenErrors :: [(LocIOCstr,SecrecError)] -> [(LocIOCstr,SecrecError)]
flattenErrors [] = []
flattenErrors ((y,MultipleErrors errs):xs) = flattenErrors (map (\e -> (y,e)) errs ++ xs)
flattenErrors (err:xs) = err : flattenErrors xs

-- we let multiple substitution constraints go through if we are not solving the last dictionary, since these constraints can always be resolved at a later time
filterScopeErrors :: ProverK Position m => SolveScope -> [(LocIOCstr,SecrecError)] -> TcM m [(LocIOCstr,SecrecError)]
filterScopeErrors scope xs = flip filterM xs $ \x -> do
    s <- cstrScope (kCstr $ unLoc $ fst x)
    return (s <= scope)

filterFailErrors :: SolveFail -> [(LocIOCstr,SecrecError)] -> [(LocIOCstr,SecrecError)]
filterFailErrors (FirstFail haltFail) xs = if haltFail then xs else filter (not . isHaltError . snd) xs
filterFailErrors (AllFail haltFail) xs = if haltFail then xs else filter (not . isHaltError . snd) xs
filterFailErrors NoFail xs = []

filterErrors :: (ProverK loc m) => loc -> SolveMode -> [(LocIOCstr,SecrecError)] -> TcM m ([(LocIOCstr,SecrecError)])
filterErrors l mode errs = do
    errs2 <- filterWarnings l errs
    errs3 <- filterScopeErrors (solveScope mode) errs2
    let errs4 = filterFailErrors (solveFail mode) errs3
    return errs4

filterWarnings :: (ProverK loc m) => loc -> [(LocIOCstr,SecrecError)] -> TcM m [(LocIOCstr,SecrecError)]
filterWarnings l = filterM $ \(k,err) -> if isOrWarnError err
    then do
        errWarn err
        removeCstr l $ unLoc k
        return False
    else return True

filterCstrSetScope :: VarsGTcM m => SolveScope -> Set LocIOCstr -> TcM m (Set LocIOCstr)
filterCstrSetScope scope = filterSetM $ \x -> do
    s <- cstrScope (kCstr $ unLoc x)
    return (s <= scope)

solveErrors :: (ProverK loc m) => loc -> SolveMode -> [(LocIOCstr,SecrecError)] -> TcM m (Maybe SecrecError)
solveErrors l mode errs = do
    errs' <- filterErrors l mode (flattenErrors errs)
    if null errs'
        then return Nothing
        -- in case there are unsolved constraints that depend on multiple substitutions, solve one
        else do
            if solveScope mode >= SolveGlobal
                then do
                    mb <- guessCstr $ filter (isHaltError . snd) errs
                    case mb of
                        -- solve the multiple substitutions constraint (it always succeeds and solves the remaining dictionary)
                        Just (Loc l iok,ks) -> do
                            --liftIO $ putStrLn $ "guessCstr " ++ ppr doAll ++ " " ++ ppr iok ++ " " ++ show (sepBy space (map pp ks))
                            catchError (solveIOCstr_ l "solveErrors" mode iok >> return Nothing) (return . Just)
                        Nothing -> return $ Just (MultipleErrors $ getErrors errs')
                else return $ Just (MultipleErrors $ getErrors errs')

guessCstr :: ProverK Position m => [(LocIOCstr,SecrecError)] -> TcM m (Maybe (LocIOCstr,[LocIOCstr]))
guessCstr errs = do
    opens <- getOpensSet
    search $ filter (\(Loc l iok,err) -> not $ Set.member (ioCstrId iok) opens) errs
  where
    search [] = return Nothing
    search (x:xs) = do
        is <- isSubst x
        if is
            then do
                let xs' = List.deleteBy (\x y -> fst x == fst y) x errs
                return $ Just (fst x,map fst xs')
            else search xs
    isSubst (Loc l iok,err) = isMultipleSubstsCstr (kCstr iok)

solveIOCstr_ :: (ProverK loc m) => loc -> String -> SolveMode -> IOCstr -> TcM m ()
solveIOCstr_ l msg mode iok = do
    catchError solve (\err -> do
        debugTc $ do
            ppiok <- ppr (ioCstrId iok)
            pperr <- ppr err
            liftIO $ putStrLn $ "nonsolvedIOCstr " ++ ppiok ++ " " ++ pperr
        throwError err)
  where
    solve = newErrorM $ resolveIOCstr_ l iok $ \k gr ctx -> do
        --olds <- State.gets (mconcat . map (mapSet (ioCstrId . unLoc) . flattenIOCstrGraphSet . tCstrs) . tDict)
        ppiok <- ppr iok
        let (ins,_,_,outs) = fromJustNote ("solveCstrNodeCtx " ++ ppiok) ctx
        --let ins'  = map (fromJustNote "ins" . Graph.lab gr . snd) ins
        --let outs' = map (fromJustNote "outs" . Graph.lab gr . snd) outs
        debugTc $ do
            opens::[Int] <- State.gets (map (ioCstrId . fst) . openedCstrs)
            ppopens <- liftM (PP.sepBy PP.comma) $ mapM pp opens
            ppiok <- ppr (ioCstrId iok)
            ppouts <- mapM (pp . snd) outs
            recs <- State.gets (mconcat . map tRec . Foldable.toList . tDict)
            doc <- liftM (vcat) $ concatMapM (mapM pp . Map.keys) $ Map.elems $ structs recs
            liftIO $ putStrLn $ "solveIOCstr " ++ show ppopens ++" --> "++ ppiok ++" --> "++ show (sepBy space ppouts) ++ " " ++ show doc
        ppiok <- ppr (ioCstrId iok)
        (res,rest) <- tcWith (locpos l) (msg ++ " solveIOCstr " ++ ppiok) $ resolveTCstr l mode (ioCstrId iok) k
        addHeadTDict l (msg++ " solveIOCstr_ " ++ ppiok) $ rest { tCstrs = Graph.empty }
        debugTc $ do
            --doc <- ppConstraints $ tCstrs rest
            doc <- liftM (vcat) $ concatMapM (mapM pp . Map.keys) $ Map.elems $ structs $ tRec rest
            ion <- ppr (ioCstrId iok)
            liftIO $ putStrLn $ "solvedIOCstr " ++ ion ++ " -->" ++ show doc
        unless (Graph.isEmpty $ tCstrs rest) $ do
            top <- buildCstrGraph l (Set.insert (ioCstrId iok) (Set.fromList $ map snd $ ins ++ outs))
            let ins' = map (fromJustNote "ins" . Graph.lab top . snd) ins
            let outs' = map (fromJustNote "outs" . Graph.lab top . snd) outs
            let rest' = tCstrs rest
            --let rest' = Graph.nfilter (\n -> not $ Set.member n olds) $ tCstrs rest
            debugTc $ do
                doc <- ppConstraints rest'
                doc1 <- ppTSubsts (tSubsts rest)
                liftIO $ putStrLn $ "solvedIOCstr rest" ++ show doc1 ++ "\n" ++ show doc
            replaceCstrWithGraph l False (ioCstrId iok) (Set.fromList ins') rest' (Set.fromList outs')
        dicts <- State.gets tDict
        debugTc $ forM_ dicts $ \d -> do
            ssd <- ppConstraints (tCstrs d)
            liftIO $ putStrLn $ "\n[" ++ show ssd ++ "\n]"
        return res

solveNewCstr_ :: ProverK loc m => loc -> SolveMode -> IOCstr -> TcM m ()
solveNewCstr_ l mode iok = newErrorM $ resolveIOCstr_ l iok (\k gr ctx -> resolveTCstr l mode (ioCstrId iok) k)

-- * Throwing Constraints

tCstrM_ :: ProverK loc m => loc -> TCstr -> TcM m ()
tCstrM_ l k = tCstrM l k >> return ()

tCstrM :: ProverK loc m => loc -> TCstr -> TcM m (Maybe IOCstr)
tCstrM l (TcK c st) = withCstrState l st $ tcCstrM l c
tCstrM l (CheckK c st) = withCstrState l st $ checkCstrM l Set.empty c
tCstrM l (HypK c st) = withCstrState l st $ hypCstrM l c

checkCstrM_ :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m ()
checkCstrM_ l deps k = checkCstrM l deps k >> return ()

checkCstrM :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m (Maybe IOCstr)
checkCstrM l deps k | isTrivialCheckCstr k = return Nothing
checkCstrM l deps k = withDeps LocalScope $ do
    addDeps "checkCstrM" LocalScope deps
    st <- getCstrState
    newTCstr l $ CheckK k st

topCheckCstrM_ :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m ()
topCheckCstrM_ l deps k = newErrorM $ checkCstrM_ l deps k

topCheckCstrM :: (ProverK loc m) => loc -> Set LocIOCstr -> CheckCstr -> TcM m (Maybe IOCstr)
topCheckCstrM l deps k = newErrorM $ checkCstrM l deps k

hypCstrM_ :: (ProverK loc m) => loc -> HypCstr -> TcM m ()
hypCstrM_ l k = hypCstrM l k >> return ()

hypCstrM :: (ProverK loc m) => loc -> HypCstr -> TcM m (Maybe IOCstr)
hypCstrM l k | isTrivialHypCstr k = return Nothing
hypCstrM l k = do
    st <- getCstrState
    newTCstr l $ HypK k st

topHypCstrM_ :: (ProverK loc m) => loc -> HypCstr -> TcM m ()
topHypCstrM_ l k = newErrorM $ hypCstrM_ l k

topHypCstrM :: (ProverK loc m) => loc -> HypCstr -> TcM m (Maybe IOCstr)
topHypCstrM l k = newErrorM $ hypCstrM l k

tcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()
tcCstrM_ l k = tcCstrM l k >> return ()

tcCstrM :: (ProverK loc m) => loc -> TcCstr -> TcM m (Maybe IOCstr)
tcCstrM l k | isTrivialTcCstr k = return Nothing
tcCstrM l k = do
    debugTc $ do
        ppl <- ppr l
        ppk <- ppr k
        liftIO $ putStrLn $ "tcCstrM " ++ ppl ++ " " ++ ppk
    st <- getCstrState
    k <- newTCstr l $ TcK k st
    --gr <- liftM (tCstrs . headNe . tDict) State.get
    --doc <- ppConstraints gr
    --debugTc $ liftIO $ putStrLn $ "tcCstrMexit " ++ pprid (maybe (-1) ioCstrId k)
    return k

topTcCstrM_ :: (ProverK loc m) => loc -> TcCstr -> TcM m ()
topTcCstrM_ l k = newErrorM $ tcCstrM_ l k
    
newTCstr :: (ProverK loc m) => loc -> TCstr -> TcM m (Maybe IOCstr)
newTCstr l k = do
    deps <- getDeps
    iok <- newTemplateConstraint l k
    debugTc $ liftIO $ putStrLn $ "newTCstr: " ++ pprid (ioCstrId iok)
    addIOCstrDependenciesM l True deps (Loc (locpos l) iok) Set.empty
    
    isGlobal <- isGlobalCstr k
    if isGlobal
        then return (Just iok)
        else catchError
            (defaultSolveMode >>= \mode -> do
                solveNewCstr_ l mode iok
                debugTc $ liftIO $ putStrLn $ "success newTCstr: " ++ pprid (ioCstrId iok)
                return Nothing
            )
            (\e -> if (isHaltError e)
                then do
                    debugTc $ liftIO $ putStrLn $ "halted newTCstr: " ++ pprid (ioCstrId iok)
                    return (Just iok)
                else do
                    debugTc $ liftIO $ putStrLn $ "failed newTCstr: " ++ pprid (ioCstrId iok)
                    throwError e
            )
                
resolveTCstr :: (ProverK loc m) => loc -> SolveMode -> Int -> TCstr -> TcM m ShowOrdDyn
resolveTCstr l mode kid (TcK k st) = liftM ShowOrdDyn $ withDeps GlobalScope $ withCstrState l st $ do
    resolveTcCstr l mode kid k
resolveTCstr l mode kid (HypK h st) = liftM ShowOrdDyn $ withDeps GlobalScope $ withCstrState l st $ do
    resolveHypCstr l mode h
resolveTCstr l mode kid (CheckK c st) = liftM ShowOrdDyn $ withDeps GlobalScope $ withCstrState l st $ do
    resolveCheckCstr l mode c

-- tests if a constraint is only used as part of an hypothesis
--isHypInGraph :: Int -> IOCstrGraph loc -> Bool
--isHypInGraph kid gr = case Graph.match kid gr of
--    (Nothing,gr') -> False
--    (Just (_,_,(kCstr . unLoc) -> HypK {},_),gr') -> True
--    (Just (_,_,_,outs),gr') -> all (flip isHypInGraph gr' . snd) outs

resolveTcCstr :: (ProverK loc m) => loc -> SolveMode -> Int -> TcCstr -> TcM m ()
resolveTcCstr l mode kid k = do
--    gr <- liftM (tCstrs . headNe . tDict) State.get
--    let warn = isHypInGraph kid gr
--    liftIO $ putStrLn $ "resolve " ++ show warn ++ " " ++ ppr k
--    if warn then newErrorM $ orWarn_ $ resolveTcCstr' k else 
    resolveTcCstr' kid k
  where
    resolveTcCstr' kid k@(TDec isCtx entries n@(TIden tn) args x) = do
        ppn <- pp n
        ppargs <- mapM pp args
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (ppn <+> parens (sepBy comma ppargs)))) $ do
            isAnn <- getAnn
            isLeak <- getLeak
            let decK = if isCtx then (==DecTypeCtx) else (const True)
            res <- matchTemplate l entries kid (TIden tn) (Just args) Nothing Nothing (checkType decK isAnn isLeak $ fmap (const l) $ TypeName () tn)
            unifiesDec l x res
    resolveTcCstr' kid k@(PDec isCtx entries n@(PIden pn) specs args r x) = do
        ppr <- pp r
        ppn <- pp n
        ppargs <- mapM pp args
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (ppr <+> ppn <+> parens (sepBy comma ppargs)))) $ do
            isAnn <- getAnn
            isLeak <- getLeak
            kind <- getKind
            let decK = if isCtx then (==DecTypeCtx) else (const True)
            res <- matchTemplate l entries kid (PIden pn) specs (Just args) (Just r) (checkProcedureFunctionLemma decK isAnn isLeak kind $ ProcedureName l $ PIden pn)
            --doc <- ppConstraints =<< liftM (tCstrs . headNe . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate " ++ ppr n ++ " " ++ show doc
            unifiesDec l x res
            --doc <- ppConstraints =<< liftM (tCstrs . headNe . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate2 " ++ ppr n ++ " " ++ show doc
    resolveTcCstr' kid k@(PDec isCtx entries o@(OIden on) specs args r x) = do
        ppr <- pp r
        ppo <- pp o
        ppargs <- mapM pp args
        addErrorM l (TypecheckerError (locpos l) . TemplateSolvingError (quotes (ppr <+> ppo <+> parens (sepBy comma ppargs)))) $ do
            isAnn <- getAnn
            isLeak <- getLeak
            k <- getKind
            let decK = if isCtx then (==DecTypeCtx) else (const True)
            res <- matchTemplate l entries kid o specs (Just args) (Just r) (checkOperator decK isAnn isLeak k $ fmap (const l) on)
            --doc <- ppConstraints =<< liftM (tCstrs . headNe . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate " ++ ppr o ++ " " ++ show doc
            unifiesDec l x res
            --doc <- ppConstraints =<< liftM (tCstrs . headNe . tDict) State.get
            --liftIO $ putStrLn $ "matchTemplate2 " ++ ppr o ++ " " ++ show doc
    resolveTcCstr' kid k@(Equals t1 t2) = do
        equals l t1 t2
    resolveTcCstr' kid k@(Coerces bvs e1 x2) = do
        opts <- askOpts
        st <- getCstrState
        ppk <- ppr k
        if checkCoercion (implicitCoercions opts) st
            then coerces l bvs e1 x2
            else unifiesExpr l (varExpr x2) e1
    --resolveTcCstr' kid k@(CoercesN exs) = do
    --    opts <- askOpts
    --    st <- getCstrState
    --    if checkCoercion (implicitCoercions opts) st
    --        then coercesN l exs
    --        else do
    --            unifiesN l $ map (loc . fst) exs
    --            assignsExprTys l exs
    resolveTcCstr' kid k@(CoercesLit e) = do
        ppe <- ppExprTy e
        let msg = text "Failed to coerce expression " <+> ppe
        addErrorM l (TypecheckerError (locpos l) . GenTcError msg . Just) $ do
            coercesLit l e
    resolveTcCstr' kid k@(Unifies t1 t2) = do
        unifies l t1 t2
    resolveTcCstr' kid k@(Assigns t1 t2) = do
        assigns l t1 t2
    resolveTcCstr' kid k@(TypeBase t x) = do
        BaseT b <- typeBase l t
        unifiesBase l x b
    resolveTcCstr' kid k@(SupportedPrint t xs) = do
        isSupportedPrint l t xs
    resolveTcCstr' kid k@(ProjectStruct t a x) = do
        ppt <- pp t
        ppa <- pp a
        ppx <- pp x
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedFieldProjection (ppt) (ppa <+> char '=' <+> ppx))
            (do
                res <- projectStructField l t a
                unifies l x (ComplexT res)
            )
    resolveTcCstr' kid k@(ProjectMatrix ct rngs x) = do
        ct' <- ppM l ct
        rngs' <- ppArrayRangesM l rngs
        x' <- ppM l x
        addErrorM l
            (TypecheckerError (locpos l) . UnresolvedMatrixProjection ct' (brackets rngs' <+> char '=' <+> x'))
            (do
                res <- projectMatrixType l ct rngs
                unifies l x res
            )
    resolveTcCstr' kid (MatchTypeDimension t d) = matchTypeDimension l t d
    resolveTcCstr' kid (IsValid c) = do
        x <- ppM l c
        addErrorM l (TypecheckerError (locpos l) . IndexConditionNotValid x) $ do
            ic <- prove l "resolve isValid" $ expr2SimpleIExpr $ fmap (Typed l) c
            isValid l ic
    resolveTcCstr' kid (NotEqual e1 e2) = do
        x <- ppM l e1
        y <- ppM l e2
        addErrorM l (TypecheckerError (locpos l) . IndexConditionNotValid (x <+> text "!=" <+> y)) $ do
            i1 <- prove l "resolve notEqual" $ expr2SimpleIExpr $ fmap (Typed l) e1
            i2 <- prove l "resolve notEqual" $ expr2SimpleIExpr $ fmap (Typed l) e2
            isValid l $ IBinOp INeq i1 i2
    resolveTcCstr' kid (IsPublic b t) = do
        isPublic l b t
    resolveTcCstr' kid (IsPrivate b t) = do
        isPrivate l b t
    resolveTcCstr' kid (ToMultiset t x) = do
        ct <- toMultisetType l t
        unifiesComplex l x ct
    resolveTcCstr' kid (Resolve t) = do
        resolve l t
    resolveTcCstr' kid (Default szs e) = do
        ppl <- pp (loc e)
        pps <- pp szs
        let msg = text "failed to resolve default expression for" <+> ppl <+> pps
        addErrorM l (TypecheckerError (locpos l) . GenTcError msg . Just) $ do
            let t = loc e
            res <- defaultExpr l t szs
            unifiesExpr l e res
    resolveTcCstr' kid k = do
        ppkid <- ppr kid
        ppk <- ppr k
        error $ "resolveTcCstr: " ++ ppkid ++ " " ++ ppk

resolve :: ProverK loc m => loc -> Type -> TcM m ()
resolve l (KindT s) = resolveKind l s
resolve l t = do
    ppt <- pp t
    genTcError (locpos l) $ text "failed to resolve" <+> ppt

resolveKind :: ProverK loc m => loc -> KindType -> TcM m ()
resolveKind l PublicK = return ()
resolveKind l (PrivateK {}) = return ()
resolveKind l k@(KVar v@(varIdWrite -> False) isPriv) = return ()
resolveKind l k@(KVar v@(varIdRead -> True) isPriv) = do
    mb <- tryResolveKVar l v isPriv
    case mb of
        Just k' -> resolveKind l k'
        Nothing -> do
            ppk <- pp k
            throwTcError (locpos l) $ TypecheckerError (locpos l) $ Halt $ GenTcError (text "failed to resolve kind" <+> ppk) Nothing
resolveKind l k = do
    ppk <- pp k
    genTcError (locpos l) $ text "failed to resolve kind" <+> ppk

resolveHypCstr :: (ProverK loc m) => loc -> SolveMode -> HypCstr -> TcM m (Maybe IExpr)
resolveHypCstr l mode hyp = do
    if solveScope mode < SolveAll -- if we don't need to solve all constraints we accept no less than solving the hypothesis
        then do
            pph <- pp hyp
            newErrorM $ addErrorM l (TypecheckerError (locpos l) . FailAddHypothesis (pph)) $ orWarn $ resolveHypCstr' hyp
        else liftM Just $ resolveHypCstr' hyp
  where
    resolveHypCstr' (HypCondition c) = expr2SimpleIExpr $ fmap (Typed l) c
    resolveHypCstr' (HypNotCondition c) = liftM (IUnOp INot) $ expr2SimpleIExpr $ fmap (Typed l) c
    resolveHypCstr' (HypEqual e1 e2) = do
        i1 <- expr2SimpleIExpr $ fmap (Typed l) e1
        i2 <- expr2SimpleIExpr $ fmap (Typed l) e2
        return $ IBinOp (IEq) i1 i2
    
resolveCheckCstr :: (ProverK loc m) => loc -> SolveMode -> CheckCstr -> TcM m ()
resolveCheckCstr l mode k = do
    ppk <- pp k
    addErrorM l (OrWarn . TypecheckerError (locpos l) . StaticAssertionFailure (ppk)) $ do
        resolveCheckCstr' k
  where
    resolveCheckCstr' (CheckAssertion c) = checkAssertion l c

ioCstrResult :: (Hashable a,IsScVar (TcM m) a,MonadIO m,Location loc) => loc -> IOCstr -> Proxy a -> TcM m (Maybe a)
ioCstrResult l iok proxy = do
    st <- readCstrStatus (locpos l) iok
    case st of
        Evaluated rest (frees,delfrees) t -> liftM Just $ cstrResult l (kCstr iok) proxy t
        Erroneous err -> return Nothing
        Unevaluated -> return Nothing
    where
    cstrResult :: (Hashable a,IsScVar (TcM m) a,Monad m,Location loc) => loc -> TCstr -> Proxy a -> ShowOrdDyn -> TcM m a
    cstrResult l k (Proxy::Proxy t) dyn = case fromShowOrdDyn dyn of
        Nothing -> do
            ppk <- pp k
            genError (locpos l) $ text "Wrong IOCstr output type" <+> text (show dyn) <+> text "::" <+> text (show $     applyShowOrdDyn Generics.typeOf dyn) <+> text "with type" <+> text (show $ Generics.typeOf (error "applyShowOrdDyn"::t)) <+> ppk
        Just x -> return x

tcProve :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict)
tcProve l msg m = do
    mode <- defaultSolveMode
    tcProveWith l msg mode m

tcProveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m (a,TDict)
tcProveWith l msg mode m = do
    newDict l $ "tcProve " ++ msg
    x <- m
    solveWith l msg mode
    d <- liftM (headNe . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (ConsNe x xs) = xs

tcProveTop :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m (a,TDict)
tcProveTop l msg m = do
    newDict l $ "tcProve " ++ msg
    x <- m
    solveTop l msg
    d <- liftM (headNe . tDict) State.get
    State.modify $ \e -> e { tDict = dropDict (tDict e) }
    return (x,d)
  where
    dropDict (ConsNe x xs) = xs

proveWith :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m (a,TDict)
proveWith l msg mode proof = tcProveWith l msg mode proof

orError :: ProverK Position m => TcM m a -> TcM m (Either SecrecError a)
orError m = liftM Right m `catchError` (return . Left)

proveWithMode :: (ProverK loc m) => loc -> String -> SolveMode -> TcM m a -> TcM m a
proveWithMode l msg mode m = do
    (a,dict) <- tcProveWith l msg mode m
    addHeadTDict l (msg++" proveWithMode") dict
    return a
    
prove :: (ProverK loc m) => loc -> String -> TcM m a -> TcM m a
prove l msg m = do
    mode <- defaultSolveMode
    proveWithMode l msg mode m

-- * Solving constraints

-- labels = variables, edges = maybe constraints
type VarGr = Graph.Gr VarIdentifier (Maybe LocIOCstr)

buildVarGr :: ProverK loc m => loc -> State.StateT (Int,Map VarIdentifier Int) (TcM m) VarGr
buildVarGr l = do
    ds <- lift $ State.gets tDict
    let addSubsts g (TSubsts ss) = foldM addSubst g $ Map.toList ss
        addSubst g (key,val) = do
            vals <- lift $ usedVs val
            addDirEdges g key (Set.toList vals)
        addCstrs g ks = foldM addCstr g $ Set.toList $ flattenIOCstrGraphSet ks
        addCstr g iok@(Loc l k) = do
            vals <- lift $ usedVs $ kCstr k
            addEdges g (Just iok) (Set.toList vals)
        addDirEdges g k [] = return g
        addDirEdges g k (v:vs) = do
            g' <- addDirEdge g k v
            addDirEdges g' k vs
        addDirEdge g k v = do
            (g1,nk) <- newNode g k
            (g2,nv) <- newNode g1 v
            return $ Graph.insEdge (nv,nk,Nothing) g2
        addEdges g mb [] = return g
        addEdges g mb [x] = addEdge g mb x x
        addEdges g mb (x:y:zs) = do
            g' <- addEdge g mb x y
            addEdges g' mb (y:zs)
        addEdge g mb x y = do
            (g1,nx) <- newNode g x
            (g2,ny) <- newNode g1 y
            return $ Graph.insEdge (nx,ny,mb) $ Graph.insEdge (ny,nx,mb) g2
        newNode g x = do
            (i,st) <- State.get
            case Map.lookup x st of
                Just n -> return (g,n)
                Nothing -> do
                    State.put (succ i,Map.insert x i st)
                    return (Graph.insNode (i,x) g,i)
        mk g d = do
            g' <- addCstrs g (tCstrs d)
            addSubsts g' (tSubsts d)
    foldM mk Graph.empty ds

reachableVarGr :: Map VarIdentifier Int -> VarGr -> (Set VarIdentifier,Set LocIOCstr)
reachableVarGr cs g = mconcatpair $ Graph.preorderF (Graph.dffWith getCstrs (Map.elems cs) g)
    where
    mconcatpair xys = let (x,y) = unzip xys in (mconcat x `mappend` Map.keysSet cs,mconcat y)
    getCstrs (froms,n,v,tos) = (Set.singleton v,Set.fromList $ (catMaybes $ map fst froms) ++ (catMaybes $ map fst tos))

relatedCstrs :: ProverK loc m => loc -> [Int] -> Set VarIdentifier -> (Set LocIOCstr -> TcM m (Set LocIOCstr)) -> TcM m (Set VarIdentifier,Set LocIOCstr)
relatedCstrs l kids vs filter = do
    (vgr,(_,st)) <- State.runStateT (buildVarGr l) (0,Map.empty)
--    debugTc $ do
--        ds <- State.gets (tDict)
--        forM_ ds $ \d -> do
--            ppd <- pp d
--            liftIO $ putStrLn $ "relatedCstrsDict " ++ show ppd
--        ppg <- ppGrM' pp pp vgr
--        liftIO $ putStrLn $ "relatedCstrs " ++ show ppg
    -- note: we don't need to solve nested multiplesubstitutions, since they are guaranteed to succeed later
    dependents <- dependentCstrs l kids
    let (relvs,relcs) = reachableVarGr (Map.intersection st $ Map.fromSet (const "msubsts") vs) vgr
    filteredcs <- filter relcs
--    debugTc $ do
--        ppvs <- liftM (sepBy space) $ mapM pp $ Set.toList relvs
--        liftIO $ putStrLn $ "relatedCstrs " ++ show ppvs
    return (relvs,Set.difference filteredcs dependents)

multipleSubstitutions :: (ProverK loc m,Vars GIdentifier (TcM m) a) => loc -> Int -> SolveScope -> a -> Either Bool (TypeClass -> Bool) -> [((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m (Set LocIOCstr,d),Doc))] -> TcM m d
multipleSubstitutions l kid scope bv testKO ss = do
    opts <- askOpts
    bvs <- usedVs' bv -- variables bound by the multiple substitutions
    debugTc $ do
        ppbvs <- ppr bvs
        liftIO $ putStrLn $ "multipleSubstitutions " ++ show kid ++ " bounds: " ++ show (backtrack opts) ++ " " ++ ppbvs
    (rvs,cs) <- relatedCstrs l [kid] bvs (filterCstrSetScope scope)
    let tokvs = tokVars rvs
    ko <- case testKO of
        Left ko -> return ko
        Right pcl -> hasAmbiguousTpltTokVars l pcl tokvs
    when ko $ do
        pptokvs <- liftM (sepBy space) $ mapM pp $ Set.toList tokvs
        tcError (locpos l) $ Halt $ GenTcError (text "did not try to solve multiple substitutions in the presence of ambiguous tokens" <+> pptokvs) Nothing
    debugTc $ do
        pptokvs <- liftM (sepBy space) $ mapM pp $ Set.toList tokvs
        ppcs <- liftM (sepBy space) $ mapM (pp . ioCstrId . unLoc) $ Set.toList cs
        liftIO $ putStrLn $ "multipleSubstitutions " ++ show kid ++ " constraints: " ++ show (backtrack opts) ++ " " ++ show ppcs ++ " with tokens " ++ show pptokvs
    --liftIO $ putStrLn $ ppr l ++ " multiple substitutions "++show kid ++" "++ ppr (sepBy comma $ map (pp . fst3) ss)
    --let removes = do
    --    let fs = Set.unions $ map fou4 ss
    --    forM_ fs $ removeFree ("multipleSubstitutions "++show kid)
    case backtrack opts of
        FullB -> do
            ok <- newErrorM $ matchAll l kid scope cs ss (matchOne l kid scope cs) []
            case ok of
                Left d -> {-removes >> -} return d
                Right errs -> tcError (locpos l) $ MultipleTypeSubstitutions errs
        TryB -> do
            ok <- newErrorM $ matchAll l kid scope cs ss (matchHead l kid True scope cs) []
            case ok of
                Left y -> newErrorM $ matchBody l kid scope cs y >>= \d -> {-removes >> -}return d
                Right errs -> tcError (locpos l) $ MultipleTypeSubstitutions errs
        NoneB -> tcError (locpos l) $ Halt $ GenTcError (text "did not try to solve multiple substitutions" <+> ppid kid) Nothing
    
matchAll :: (ProverK loc m) => loc -> Int -> SolveScope -> Set LocIOCstr -> [((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m (Set LocIOCstr,d),Doc))] -> (((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m (Set LocIOCstr,d),Doc)) -> TcM m x) -> [(Doc,SecrecError)] -> TcM m (Either x [(Doc,SecrecError)])
matchAll l kid scope cs [] match errs = return $ Right errs
matchAll l kid scope cs (x:xs) match errs = catchError
    -- match and solve all remaining constraints
    (proveWithMode l "match" (SolveMode (FirstFail True) scope) $ liftM Left $ match x)
    -- backtrack and try another match
    (\e -> do
        debugTc $ do
            pe <- ppr e
            liftIO $ putStrLn $ "failed " ++ show (snd (fst3 x)) ++ " " ++ pe
        matchAll l kid scope cs xs match (errs++[(snd (fst3 x),e)])
        --throwError e
    )

matchOne :: (ProverK loc m) => loc -> Int -> SolveScope -> Set LocIOCstr -> ((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m (Set LocIOCstr,d),Doc)) -> TcM m d
matchOne l kid scope cs (match,deps,post) = do
    res <- matchHead l kid False scope cs (match,deps,post)
    matchBody l kid scope cs res

matchHead :: (ProverK loc m) => loc -> Int -> Bool -> SolveScope -> Set LocIOCstr -> ((TcM m b,Doc),(b -> TcM m c,Doc),(c -> TcM m (Set LocIOCstr,d),Doc)) -> TcM m ((b,Set LocIOCstr),(b -> TcM m c,Doc),(c -> TcM m (Set LocIOCstr,d),Doc))
matchHead l kid noHalt scope cs (match,deps,post) = do
--    forSetM_ cs $ \(Loc _ iok) -> liftIO $ readIdRef (kStatus iok) >>= \st -> case st of
--            Erroneous _ -> writeIdRef (kStatus iok) Unevaluated
--            otherwise -> return ()
    debugTc $ do
        ppl <- ppr l
        liftIO $ putStrLn $ ppl ++ " trying to match head"++show kid ++ " " ++ show scope ++ " " ++ show (snd match)
    mode <- defaultSolveMode
    let fail' = if noHalt then mkHaltFail (solveFail mode) else solveFail mode
    (b,ks) <- proveWithMode l ("matchOneHead"++show kid) (mode { solveScope = scope, solveFail = fail' }) $ tcWithCstrs l ("matchOneHead"++show kid) (fst match)
    return ((b,ks),deps,post)

matchBody :: (ProverK loc m) => loc -> Int -> SolveScope -> Set LocIOCstr -> ((b,Set LocIOCstr),(b -> TcM m c,Doc),(c -> TcM m (Set LocIOCstr,d),Doc)) -> TcM m d
matchBody l kid scope cs ((b,ks),deps,post) = do
    debugTc $ do
        ppl <- ppr l
        liftIO $ putStrLn $ ppl ++ " trying to match "++ show scope ++ " " ++ show kid
    mode <- defaultSolveMode
    
    -- solve dependencies
    c <- proveWithMode l ("matchOneHead"++show kid) (mode { solveScope = scope }) $ withDependencies ks ((fst deps) b)
    
    -- prepare body
    (cs',d) <- withDependencies ks ((fst post) c)
    
    let cs'' = Set.union cs cs'
    opts <- askOpts
    case backtrack opts of
        FullB -> do -- solve body and all other dependencies
            solveSelectionWith l ("matchone"++show kid) (mode { solveFail = FirstFail True, solveScope = scope }) cs''
            debugTc $ liftIO $ putStrLn $ "matchOne solved " ++ show kid
        otherwise -> do -- just add the constraints to be solved later
            return ()
    return d

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

--tryNot :: ProverK loc m => loc -> [TCstr] -> TcM m (Either SecrecError SecrecError)
--tryNot = undefined

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
equals l (TType isNotVoid1) (TType isNotVoid2) = return ()
equals l DType DType = return ()
equals l (BType c1) (BType c2) | c1 == c2 = return ()
equals l (KType c1) (KType c2) | c1 == c2 = return ()
equals l (VAType b1 sz1) (VAType b2 sz2) = do
    tcCstrM_ l $ Equals b1 b2
    equalsExprTy l sz1 sz2
equals l (KindT k1) (KindT k2) = equalsKind l k1 k2
equals l (StmtType s1) (StmtType s2) | s1 == s2 = return ()
--equals l (CondType t1 c1) (CondType t2 c2) = do
--    equals l t1 t2
--    equalsExprTy l False c1 c2
equals l (VArrayT a1) (VArrayT a2) = equalsArray l a1 a2
equals l t1 t2 = constraintError (EqualityException "type") l t1 pp t2 pp Nothing

equalsKind :: (ProverK loc m) => loc -> KindType -> KindType -> TcM m ()
equalsKind l PublicK PublicK = return ()
equalsKind l (KVar k1 priv1) (KVar k2 priv2) | k1 == k2 = return ()
equalsKind l (KVar k1@(varIdRead -> True) priv1) k2 = do
    k1' <- resolveKVar l k1 priv1
    tcCstrM_ l $ Equals (KindT k1') (KindT k2)
equalsKind l k1 (KVar k2@(varIdRead -> True) priv2) = do
    k2' <- resolveKVar l k2 priv2
    tcCstrM_ l $ Equals (KindT k1) (KindT k2')
equalsKind l (PrivateK k1) (PrivateK k2) | k1 == k2 = return ()
equalsKind l k1 k2 = constraintError (EqualityException "kind") l k1 pp k2 pp Nothing

equalsArray :: (ProverK loc m) => loc -> VArrayType -> VArrayType -> TcM m ()
equalsArray l (VAVal ts1 b1) (VAVal ts2 b2) = do
    equalsList l ts1 ts2
    tcCstrM_ l $ Equals b1 b2
equalsArray l (VAVar v1@(varIdRead -> True) b1 sz1) a2 = do
    a1' <- resolveVAVar l v1 b1 sz1
    equalsArray l a1' a2
equalsArray l a1 (VAVar v2@(varIdRead -> True) b2 sz2) = do
    a2' <- resolveVAVar l v2 b2 sz2
    equalsArray l a1 a2'
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
equalsSec l (SVar v1 k1) (SVar v2 k2) | v1 == v2 = equalsKind l k1 k2
equalsSec l (SVar v@(varIdRead -> True) k1) s2 = do
    s1 <- resolveSVar l v k1
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 (SVar v@(varIdRead -> True) k2) = do
    s2 <- resolveSVar l v k2
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
equalsSec l s1 s2 = constraintError (EqualityException "security type") l s1 pp s2 pp Nothing

equalsDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m ()
equalsDec l d1 d2 = readable2 equalsDec' l d1 d2
    where
    equalsDec' (DVar v1) (DVar v2) | v1 == v2 = return ()
    equalsDec' d1 d2 | isJust (decTypeTyVarId d1) && decTypeTyVarId d1 == decTypeTyVarId d2 = return ()
    equalsDec' d1@(DecType i1 isRec1 _ _ _ tspecs1 _) d2@(DecType i2 isRec2 _ _ _ tspecs2 _) | isRec1 == isRec2 = do
        equalsTpltArgs l tspecs1 tspecs2
    equalsDec' d1 d2 = do
        p1 <- ppr (decTypeTyVarId d1)
        p2 <- ppr (decTypeTyVarId d2)
        constraintError (EqualityException ("declaration type " ++ p1 ++ " " ++ p2)) l d1 pp d2 pp Nothing

equalsComplex :: (ProverK loc m) => loc -> ComplexType -> ComplexType -> TcM m ()
--equalsComplex l (TyLit l1) (TyLit l2) | l1 == l2 = return ()
--equalsComplex l (ArrayLit es1) (ArrayLit es2) = do
--    constraintList (EqualityException "size") (equalsExprTy l) l es1 es2
--    return ()
equalsComplex l (CType s1 t1 d1) (CType s2 t2 d2) = do
    tcCstrM_ l $ Equals (SecT s1) (SecT s2)
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
    equalsExprTy l d1 d2
equalsComplex l (CVar v1 _) (CVar v2 _) | v1 == v2 = return ()
equalsComplex l (CVar v@(varIdRead -> True) k1) c2 = do
    c1 <- resolveCVar l v k1
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l c1 (CVar v@(varIdRead -> True) k2) = do
    c2 <- resolveCVar l v k2
    tcCstrM_ l $ Equals (ComplexT c1) (ComplexT c2)
equalsComplex l Void Void = return ()
equalsComplex l c1 c2 = constraintError (EqualityException "complex type") l c1 pp c2 pp Nothing

equalsBase :: (ProverK loc m) => loc -> BaseType -> BaseType -> TcM m ()
equalsBase l (BVar v1 c1) (BVar v2 c2) | v1 == v2 = return ()
equalsBase l (BVar v@(varIdRead -> True) c1) t2 = do
    t1 <- resolveBVar l v c1
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l t1 (BVar v@(varIdRead -> True) c2) = do
    t2 <- resolveBVar l v c2
    tcCstrM_ l $ Equals (BaseT t1) (BaseT t2)
equalsBase l (TApp (TIden n1) ts1 d1) (TApp (TIden n2) ts2 d2) = do
    equalsTIdentifier l (TIden n1) (TIden n2)
    equalsTpltArgs l ts1 ts2
    --equalsDec l d1 d2
equalsBase l (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
equalsBase l (MSet b1) (MSet b2) = equalsBase l b1 b2
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

expandCTypeVar :: (ProverK loc m) => loc -> VarIdentifier -> Bool -> TcM m ComplexType
expandCTypeVar l v@(varIdWrite -> True) True = do
    k <- newKindVar "k" Nothing False Nothing
    d <- newDomainTyVar "d" k False Nothing
    t <- newBaseTyVar Nothing False Nothing
    dim <- newDimVar False Nothing
    let ct = CType d t dim 
    addSubstM l (SubstMode NoFailS True) (VarName (TType True) $ VIden v) $ ComplexT ct
    return ct

-- | Non-directed coercion for a list of expressions.
-- Returns the unified type.
-- applies substitutions
--coercesN :: ProverK loc m => loc -> [(Expr,Var)] -> TcM m ()
--coercesN l exs | all (isComplex . loc . fst) exs = do
--    exs' <- forM exs $ \(e,x) -> do
--        ct <- typeToComplexType l (loc e)
--        let e' = updLoc e (ComplexT ct)
--        return (e',x)
--    coercesNComplex l exs'
--coercesN l exs = do
--    ppexs <- mapM (ppExprTy . fst) exs
--    addErrorM l (TypecheckerError (locpos l) . NCoercionException "type" Nothing (ppexs) . Just) $ do
--        unifiesN l $ map (loc . fst) exs
--        assignsExprTys l exs

--coercesNComplex :: ProverK loc m => loc -> [(Expr,Var)] -> TcM m ()
--coercesNComplex l exs | any (isVoid . unComplexT . loc . fst) exs = do
--    ppexs <- mapM (ppExprTy . fst) exs
--    addErrorM l (TypecheckerError (locpos l) . NCoercionException "complex type" Nothing (ppexs) . Just) $ do
--        unifiesN l $ map (loc . fst) exs
--        assignsExprTys l exs
--coercesNComplex l exs | any (isCVar . unComplexT . loc . fst) exs = do
--    exs' <- forM exs $ rec True
--    coercesNComplex l exs'
--  where
--    rec True (e,x) = case loc e of
--        ComplexT (CVar v@(varIdRead -> True) isNotVoid) -> do
--            mb <- tryResolveCVar l v isNotVoid
--            case mb of
--                Just t' -> return (updLoc e $ ComplexT t',x)
--                Nothing -> rec False (e,x)
--        ComplexT (CVar v@(varIdWrite -> True) True) -> do
--            t' <- expandCTypeVar l v True
--            return (updLoc e $ ComplexT t',x)
--        ComplexT (CVar v isNotVoid) -> do
--            ppexs <- mapM (ppExprTy . fst) exs
--            tcError (locpos l) $ Halt $ NCoercionException "complex type" Nothing (ppexs) Nothing
--        otherwise -> return (e,x)
--coercesNComplex l exs | all (isCType . unComplexT . loc . fst) exs = do
--    ppexs <- mapM (ppExprTy . fst) exs
--    addErrorM l (TypecheckerError (locpos l) . (NCoercionException "complex type") Nothing (ppexs) . Just) $ do
--        -- we unify base types, no coercions here
--        unifiesN l $ map (BaseT . baseCType . unComplexT . loc . fst) exs
--        -- coerce security and dimension types
--        coercesNSecDimSizes l exs
--coercesNComplex l exs = do
--    ppexs <- mapM (ppExprTy . fst) exs
--    tcError (locpos l) $ NCoercionException "complex type" Nothing (ppexs) Nothing

--coercesNSecDimSizes :: (ProverK loc m) => loc -> [(Expr,Var)] -> TcM m ()
--coercesNSecDimSizes l [] = return ()
--coercesNSecDimSizes l exs = do
--    let cts = map (unComplexT . loc . fst) exs
--    s3 <- maxSec l $ map secCType cts
--    let b3 = baseCType $ head cts
--    d3 <- maxDim l $ map dimCType cts
--    let t3 = ComplexT $ CType s3 b3 d3
--    -- coerce each expression individually
--    forM_ exs $ \(e,x) -> do
--        tcCstrM_ l $ Unifies (loc x) t3
--        coercesSecDimSizes l Nothing e x

maxSec :: ProverK loc m => loc -> [SecType] -> TcM m SecType
maxSec l ss = do
    maxs <- maximumsSec l ss []
    case maxs of
        [s] -> return s
        (SVar v k:_) -> newDomainTyVar "smax" k False Nothing
        (s:_) -> return s

maximumsSec :: ProverK loc m => loc -> [SecType] -> [SecType] -> TcM m [SecType]
maximumsSec l [] maxs = return maxs
maximumsSec l (s:ss) [] = maximumsSec l ss [s]
maximumsSec l (s:ss) maxs@(max:_) = do
    cmp <- tcBlock $ comparesSec l True s max
    case compOrdering cmp of
        (LT,isLat,ko) -> maximumsSec l ss maxs
        (EQ,isLat,ko) -> maximumsSec l ss (s:maxs)
        (GT,isLat,ko) -> maximumsSec l ss [s]

maxDim :: ProverK loc m => loc -> [Expr] -> TcM m Expr
maxDim l ds = do
    maxs <- maximumsDim l ds []
    case maxs of
        [d] -> return d
        otherwise -> newDimVar False Nothing 

maximumsDim :: ProverK loc m => loc -> [Expr] -> [Expr] -> TcM m [Expr]
maximumsDim l [] maxs = return maxs
maximumsDim l (s:ss) [] = maximumsDim l ss [s]
maximumsDim l (s:ss) maxs@(max:_) = do
    cmp <- tcBlock $ comparesDim l True s max
    case compOrdering cmp of
        (LT,isLat,ko) -> maximumsDim l ss maxs
        (EQ,isLat,ko) -> maximumsDim l ss (s:maxs)
        (GT,isLat,ko) -> maximumsDim l ss [s]

tcTop_ :: ProverK l m => l -> Bool -> TcCstr -> TcM m ()
tcTop_ l isTop = if isTop then topTcCstrM_ l else tcCstrM_ l

resolveMultipleSubstitutions :: ProverK loc m => loc -> Maybe Bool -> [Type] -> [(TcM m (),TcM m ())] -> TcM m ()
resolveMultipleSubstitutions l ko v s = do
    kid <- State.gets (ioCstrId . fst . head . openedCstrs)
    let mkSubst (x,y) = do
        let match = x
        let post () = do
            ((),cs) <- tcWithCstrs l "multiple" y
            return (cs,())
        return ((match,empty),(return,PP.empty),(post,empty))
    s' <- mapM mkSubst s
    let ko' = case ko of
                Just b -> Left b
                Nothing -> Right (\cl -> any ((==cl) . typeClass "") v)
    multipleSubstitutions l kid SolveAll v ko' s'

tcCoercesN :: ProverK loc m => loc -> Bool -> [Expr] -> Type -> TcM m [Expr]
tcCoercesN l isTop es t = do
    forM es $ \e -> tcCoerces l isTop Nothing e t

tcCoerces :: ProverK loc m => loc -> Bool -> Maybe [Type] -> Expr -> Type -> TcM m Expr
tcCoerces l isTop bvs e t = do
    opts <- askOpts
    st <- getCstrState
    let doCoerce = checkCoercion (implicitCoercions opts) st
    debugTc $ do
        ppe <- pp e
        ppt <- pp t
        liftIO $ putStrLn $ "tcCoerces " ++ show doCoerce ++ " " ++ show ppe ++ " " ++ show ppt
    if doCoerce
        then coercesE l isTop bvs e t
        else do
            tcTop_ l isTop $ Unifies (loc e) t
            return e

coercesE :: (ProverK loc m) => loc -> Bool -> Maybe [Type] -> Expr -> Type -> TcM m Expr
coercesE l isTop bvs e1 t2 = do
    pp1 <- pp e1
    x2 <- newTypedVar "coerces" t2 False $ Just $ pp1
    tcTop_ l isTop $ Coerces bvs e1 x2
    return $ varExpr x2

coercesPDec :: ProverK loc m => loc -> Bool -> Expr -> Var -> TcM m ()
coercesPDec l isTop e x = do
    let tx = loc x
    implyCstrM l (pDecCstrM l Nothing isTop True False (OIden $ OpCoerce $ NoType "<~") Nothing [(False,Left e,False)] tx) $ \(dec,[(False,Left ex,False)]) -> do
        let res = UnaryExpr tx (OpCoerce $ DecT dec) ex
        tcCstrM_ l $ Unifies (IdxT $ varExpr x) (IdxT res)

implyCstrM :: ProverK loc m => loc -> TcM m a -> (a -> TcM m b) -> TcM m b
implyCstrM l m mg = withDeps LocalScope $ do
    (x,ks) <- tcWithCstrs l "implication" m
    forM_ ks $ addDep "implication" LocalScope
    mg x

-- | Directed coercion, with implicit security type coercions and literal coercions
-- applies substitutions
-- returns a classify declaration
coerces :: (ProverK loc m) => loc -> Maybe [Type] -> Expr -> Var -> TcM m ()
coerces l bvs e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(BaseT b2)) = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "base type") pp1 pp2 . Just) $ do
        assignsExprTy l x2 e1
coerces l bvs e1@(loc -> t1@(ComplexT ct1)) x2@(loc -> t2@(ComplexT ct2)) = coercesComplex l bvs e1 x2
coerces l bvs e1@(loc -> t1@(ComplexT c1)) x2@(loc -> t2@(BaseT b2)) = coercesComplex l bvs e1 (updLoc x2 $ ComplexT $ defCType b2)
coerces l bvs e1@(loc -> t1@(BaseT b1)) x2@(loc -> t2@(ComplexT c2)) = coercesComplex l bvs (updLoc e1 $ ComplexT $ defCType b1) x2
coerces l bvs e1@(loc -> t1) x2@(loc -> t2) | isVATy t1 || isVATy t2 = coercesArray l bvs e1 x2
coerces l bvs e1 x2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "type") pp1 pp2 . Just) $ do
        assignsExprTy l x2 e1

coercesArray :: (ProverK loc m) => loc -> Maybe [Type] -> Expr -> Var -> TcM m ()
coercesArray l bvs e1 x2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "array") pp1 pp2 . Just) $ do
        assignsExprTy l x2 e1

coercesComplex :: (ProverK loc m) => loc -> Maybe [Type] -> Expr -> Var -> TcM m ()
coercesComplex l bvs e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT ct2) = coercesComplex' l e1 ct1 x2 ct2
    where
    coercesComplex' l e1 t1 x2 t2 = readable2 coercesComplex'' l t1 t2
    
    coercesComplex'' t1 t2 | isVoid t1 || isVoid t2 = do
        pp1 <- (ppExprTy e1)
        pp2 <- (ppExprTy x2)
        addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") pp1 pp2 . Just) $ do
            assignsExprTy l x2 e1
    coercesComplex'' ct1@(CType s1 t1 d1) ct2@(CType s2 t2 d2) = do
        pp1 <- (ppExprTy e1)
        pp2 <- (ppVarTy x2)
        addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type") pp1 pp2 . Just) $ do
            tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2) -- we unify base types, no coercions here
            coercesSecDimSizes l bvs e1 x2
    coercesComplex'' ct1@(getWritableVar -> Just (v1,isNotVoid1)) ct2 = do
        let is = max isNotVoid1 (isNotVoid ct2)
        if is
            then do
                ct1' <- expandCTypeVar l v1 is
                coercesComplex l bvs (updLoc e1 $ ComplexT ct1') x2
            else constraintError (\x y err -> Halt $ CoercionException "complex type" x y err) l e1 ppExprTy x2 ppVarTy Nothing
    coercesComplex'' ct1 (getWritableVar -> Just (v2,isNotVoid2)) = do
        let is = max isNotVoid2 (isNotVoid ct1)
        if is
            then do
                ct2' <- expandCTypeVar l v2 is
                coercesComplex l bvs e1 (updLoc x2 $ ComplexT ct2')
            else  constraintError (\x y err -> Halt $ CoercionException "complex type" x y err) l e1 ppExprTy x2 ppVarTy Nothing
    coercesComplex'' ct1 ct2 = constraintError (CoercionException "complex type") l e1 ppExprTy x2 ppVarTy Nothing

coercesSecDimSizes :: (ProverK loc m) => loc -> Maybe [Type] -> Expr -> Var -> TcM m ()
coercesSecDimSizes l bvs e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT ct2) = readable2 coercesSecDimSizes' l ct1 ct2
    where
    coercesSecDimSizes' ct1@(CType s1 b1 d1) (CType s2 b2 d2) = do
        let t3 = ComplexT $ CType s1 b2 d2 -- intermediate type
        pp1 <- pp e1
        x3 <- newTypedVar "de" t3 False $ Just $ pp1
        coercesDimSizes l bvs (updLoc e1 $ ComplexT ct1) (updLoc x3 t3)
        coercesSec l bvs (varExpr x3) (updLoc x2 $ ComplexT ct2)
    coercesSecDimSizes' ct1 ct2 = constraintError (CoercionException "complex type security dimension") l e1 ppExprTy x2 ppVarTy Nothing

mkChoiceDec :: ProverK loc m => loc -> Expr -> Var -> TcM m [(TcM m (),TcM m ())]
mkChoiceDec l e1 x2 = do
    inCtx <- getInCtx
    if inCtx
        then do
            let cont = coercesPDec l False e1 x2
            return [(return (),cont)]
        else return []

coercesDimSizes :: (ProverK loc m) => loc -> Maybe [Type] -> Expr -> Var -> TcM m ()
coercesDimSizes l bvs e1@(loc -> ComplexT ct1@(CType s1 b1 d1)) x2@(loc -> ComplexT ct2@(CType s2 b2 d2)) = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "complex type dimension") pp1 pp2 . Just) $ do
        readable2 coercesDimSizes' l d1 d2
  where
    doMulti = isNothing bvs
    coercesDimSizes' d1 d2 = do
        mb <- tryTcError l $ equalsExpr l d1 d2
        case mb of
            Right () -> assignsExprTy l x2 e1
            otherwise -> do
                opts <- askOpts
                st <- getCstrState
                mb1 <- isZeroIdxExpr l d1
                mb2 <- isZeroIdxExpr l d2
                coercesDimSizes'' opts st d1 mb1 d2 mb2
    
    coercesDimSizes'' opts st d1 _ d2 (Right True) = assignsExprTy l x2 e1
    coercesDimSizes'' opts st d1 (Right False) d2 (Right False) = assignsExprTy l x2 e1
    coercesDimSizes'' opts st d1 (Right False) d2 _ = assignsExprTy l x2 e1
    coercesDimSizes'' opts st d1 (Right True) s2 (Right False) = do
        implyCstrM l (repeatExpr l False e1 Nothing ct2) (assignsExprTy l x2)
    coercesDimSizes'' opts st d1 (Right False) d2 (Right True) = constraintError (CoercionException "complex type dimension") l e1 ppExprTy x2 ppVarTy $ Just $ GenericError (locpos l) (text "cannot coerce (>0) to 0") Nothing
    coercesDimSizes'' opts st d1 (Right True) d2 _ = if doMulti
        then tcCstrM_ l $ Coerces (Just [IdxT d2]) e1 x2
        else do
            -- d2 == 0
            let match1 = tcCstrM_ l $ match (backtrack opts) (IdxT d2) (IdxT $ indexExpr 0)
            let cont1 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice1 = (match1,cont1)
            -- d2 > 0
            let match2 = tcCstrM_ l $ NotEqual d2 (indexExpr 0)
            let cont2 = implyCstrM l (repeatExpr l False e1 Nothing ct2) (assignsExprTy l x2)
            let choice2 = (match2,cont2)
            -- 0 ~> d2
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l Nothing [IdxT d2] ([choice1,choice2] ++ choiceDec)
    coercesDimSizes'' opts st d1 mb1 d2 (Right False) = if doMulti
        then tcCstrM_ l $ Coerces (Just [IdxT d1]) e1 x2
        else do
            -- d1 == 0
            let match1 = tcCstrM_ l $ match (backtrack opts) (IdxT d1) (IdxT $ indexExpr 0)
            let cont1 = implyCstrM l (repeatExpr l False e1 Nothing ct2) (assignsExprTy l x2)
            let choice1 = (match1,cont1)
            --d1 > 0
            let match2 = tcCstrM_ l $ match (backtrack opts) (IdxT d1) (IdxT d2)
            let cont2 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice2 = (match2,cont2)
            -- d1 ~> d2
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l Nothing [IdxT d1] ([choice1,choice2] ++ choiceDec)
    coercesDimSizes'' opts st d1 _ d2 _ | isJust (getNonWritableVar d1) || isJust (getNonWritableVar d2) = if doMulti
        then tcCstrM_ l $ Coerces (Just [IdxT d1,IdxT d2]) e1 x2
        else do
            -- d1 == d2
            let match0 = tcCstrM_ l $ match (backtrack opts) (IdxT d1) (IdxT d2)
            let cont0 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice0 = (match0,cont0)
            -- d1 ~> d2
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l (Just False) [IdxT d1,IdxT d2] ([choice0] ++ choiceDec)
    coercesDimSizes'' opts st d1 mb1 d2 mb2 = if doMulti
        then tcCstrM_ l $ Coerces (Just [IdxT d1,IdxT d2]) e1 x2
        else do
            -- d1 == d2
            let match0 = tcCstrM_ l $ match NoneB (IdxT d1) (IdxT d2)
            let cont0 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice0 = (match0,cont0)
            -- 0 --> 0
            let match1 = tcCstrM_ l $ match (backtrack opts) (IdxT d1) (IdxT $ indexExpr 0)
            let cont1 = do
                tcCstrM_ l $ match (backtrack opts) (IdxT d2) (IdxT $ indexExpr 0)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice1 = (match1,cont1)
            -- 0 --> n
            let match2 = do
                tcCstrM_ l $ match (backtrack opts) (IdxT d1) (IdxT $ indexExpr 0)
                tcCstrM_ l $ NotEqual d2 (indexExpr 0)
            let cont2 = implyCstrM l (repeatExpr l False e1 Nothing ct2) (assignsExprTy l x2)
            let choice2 = (match2,cont2)
            -- n --> n
            let match3 = do
                tcCstrM_ l $ NotEqual d1 (indexExpr 0)
                tcCstrM_ l $ NotEqual d2 (indexExpr 0)
            let cont3 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice3 = (match3,cont3)
            -- d1 ~> d2
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l Nothing [IdxT d1,IdxT d2] ([choice0,choice1,choice2,choice3] ++ choiceDec)
    coercesDimSizes'' opts st d1 mb1 d2 mb2 = do
        ppmb1 <- pp mb1
        ppmb2 <- pp mb2
        constraintError (\x y mb -> Halt $ CoercionException "complex type dimension" x y mb) l e1 ppExprTy x2 ppVarTy $ Just $ GenericError (locpos l) (text "Left:" <+> ppmb1 $+$ text "Right:" <+> ppmb2) Nothing

coercesSec :: (ProverK loc m) => loc -> Maybe [Type] -> Expr -> Var -> TcM m ()
coercesSec l bvs e1@(loc -> ComplexT ct1) x2@(loc -> ComplexT t2) = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppVarTy x2)
    addErrorM l (TypecheckerError (locpos l) . (CoercionException "security type") pp1 pp2 . Just) $ do
        s2 <- cSecM l t2
        opts <- askOpts
        coercesSec' l bvs e1 ct1 x2 s2

coercesSec' :: (ProverK loc m) => loc -> Maybe [Type] -> Expr -> ComplexType -> Var -> SecType -> TcM m ()
coercesSec' l bvs e1 ct1@(cSec -> Just s1) x2 s2 = do
    mb <- tryTcError l $ equals l (SecT s1) (SecT s2)
    case mb of
        Right () -> do
            debugTc $ do
                pp1 <- ppr s1
                pp2 <- ppr s2
                liftIO $ putStrLn $ "coercesSec0 " ++ pp1 ++ " " ++ pp2
            assignsExprTy l x2 e1
        otherwise -> do
            opts <- askOpts
            st <- getCstrState
            readable2 (coercesSec'' opts st) l s1 s2
  where
    ct2 = setCSec ct1 s2
    doMulti = isNothing bvs
    coercesSec'' opts st Public Public = do
        debugTc $ do
            pp1 <- ppr s1
            pp2 <- ppr s2
            liftIO $ putStrLn $ "coercesSec1 " ++ pp1 ++ " " ++ pp2
        assignsExprTy l x2 e1
    coercesSec'' opts st s1@Public s2@(SVar v PublicK) = do
        debugTc $ do
            pp1 <- ppr s1
            pp2 <- ppr s2
            liftIO $ putStrLn $ "coercesSec2 " ++ pp1 ++ " " ++ pp2
        unifiesSec l s1 s2
        assignsExprTy l x2 e1
    coercesSec'' opts st s1@Public s2@(getWritableVar -> Just (v2,k2)) | isPrivateKind k2 = do
        implyCstrM l (classifyExpr l False e1 ct2) $ \e2 -> do
            tcCstrM l $ IsPrivate True (SecT s2)
            assignsExprTy l x2 e2
    coercesSec'' opts st s1@Public s2@(getWritableVar -> Just (v2,k2)) | not (isPrivateKind k2) = if doMulti
        then tcCstrM_ l $ Coerces (Just [SecT s2]) e1 x2
        else do
            -- s2 = public
            let match1 = tcCstrM_ l $ IsPublic (backtrack opts/=NoneB) (SecT s2)
            let cont1 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice1 = (match1,cont1)
            -- s2 = private
            let match2 = tcCstrM_ l $ IsPrivate (backtrack opts/=NoneB) (SecT s2)
            let cont2 = implyCstrM l (classifyExpr l False e1 ct2) (assignsExprTy l x2)
            let choice2 = (match2,cont2)
            -- public ~> s2
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l Nothing [SecT s2] ([choice1,choice2] ++ choiceDec)
    coercesSec'' opts st s1@(SVar v _) s2@(Public) = do
        debugTc $ do
            pp1 <- ppr s1
            pp2 <- ppr s2
            liftIO $ putStrLn $ "coercesSec3 " ++ pp1 ++ " " ++ pp2
        tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        assignsExprTy l x2 e1
    coercesSec'' opts st s1 s2 | isPrivateKind (secTypeKind s1) = do
        debugTc $ do
            pp1 <- ppr s1
            pp2 <- ppr s2
            liftIO $ putStrLn $ "coercesSec4 " ++ pp1 ++ " " ++ pp2
        tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        assignsExprTy l x2 e1
    coercesSec'' opts st s1@(SVar v1 PublicK) s2@(Private d2 k2) = do
        unifiesSec l s1 Public
        coercesSec' l bvs e1 ct1 x2 s2
    coercesSec'' opts st s1@(getWritableVar -> Just (v1,k1)) s2@(Private d2 k2) | not (isPrivateKind k1) = if doMulti
        then tcCstrM_ l $ Coerces (Just [SecT s1]) e1 x2
        else do
            -- s1 = public
            let match1 = tcCstrM_ l $ IsPublic (backtrack opts/=NoneB) (SecT s1)
            let cont1 = implyCstrM l (classifyExpr l False e1 ct2) (assignsExprTy l x2)
            let choice1 = (match1,cont1)
            -- s1 = private
            let match2 = tcCstrM_ l $ match (backtrack opts) (SecT s1) (SecT s2)
            let cont2 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice2 = (match2,cont2)
            -- s1 ~> private
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l Nothing [SecT s1] ([choice1,choice2] ++ choiceDec)
    coercesSec'' opts st s1@(SVar v1 k1) s2@(SVar v2 k2) | v1 == v2 = do
        debugTc $ do
            pp1 <- ppr s1
            pp2 <- ppr s2
            liftIO $ putStrLn $ "coercesSec5 " ++ pp1 ++ " " ++ pp2
        tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
        assignsExprTy l x2 e1
    coercesSec'' opts st s1@(getWritableVar -> Just (v1,k1)) s2@(getWritableVar -> Just (v2,k2)) = if doMulti
        then tcCstrM_ l $ Coerces (Just [SecT s1,SecT s2]) e1 x2
        else do
            -- s1 == s2
            let match0 = tcCstrM_ l $ match NoneB (SecT s1) (SecT s2)
            let cont0 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice0 = (match0,cont0)
            -- public --> public
            let match1 = do
                tcCstrM_ l $ IsPublic (backtrack opts/=NoneB) (SecT s1)
                tcCstrM_ l $ IsPublic (backtrack opts/=NoneB) (SecT s2)
            let cont1 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice1 = (match1,cont1)
            -- public --> private
            let match2 = do
                tcCstrM_ l $ IsPublic (backtrack opts/=NoneB) (SecT s1)
                tcCstrM_ l $ IsPrivate (backtrack opts/=NoneB) (SecT s2)
            let cont2 = implyCstrM l (classifyExpr l False e1 ct2) (assignsExprTy l x2)
            let choice2 = (match2,cont2)
            -- private --> private
            let match3 = do
                tcCstrM_ l $ IsPrivate (backtrack opts/=NoneB) (SecT s1)
                tcCstrM_ l $ IsPrivate (backtrack opts/=NoneB) (SecT s2)
            let cont3 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice3 = (match3,cont3)
            -- s1 ~> s2
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l Nothing [SecT s1,SecT s2] ([choice0,choice1,choice2,choice3] ++ choiceDec)
    coercesSec'' opts st Public s2@(Private d2 k2) = do
        implyCstrM l (classifyExpr l False e1 ct2) (assignsExprTy l x2)
    coercesSec'' opts st s1 s2 | isJust (getNonWritableVar s1) || isJust (getNonWritableVar s2) = if doMulti
        then tcCstrM_ l $ Coerces (Just [SecT s1,SecT s2]) e1 x2
        else do
            -- s1 == s2
            let match0 = tcCstrM_ l $ match (backtrack opts) (SecT s1) (SecT s2)
            let cont0 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice0 = (match0,cont0)
            -- s1 ~> s2
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l (Just False) [SecT s1,SecT s2] ([choice0] ++ choiceDec)
    coercesSec'' opts st Public s2@(getVar -> Just (v2,k2)) | isPrivateKind k2 = do
        implyCstrM l (classifyExpr l False e1 ct2) (assignsExprTy l x2)
    coercesSec'' opts st (getWritableVar -> Just (v1,k1)) s2@(getVar -> Just (v2,k2)) | not (isPrivateKind k1) = if doMulti
        then tcCstrM_ l $ Coerces (Just [SecT s1]) e1 x2
        else do
            let match1 = tcCstrM_ l $ IsPublic (backtrack opts/=NoneB) (SecT s1)
            let cont1 = implyCstrM l (classifyExpr l False e1 ct2) (assignsExprTy l x2)
            let choice1 = (match1,cont1)
            let match2 = tcCstrM_ l $ match (backtrack opts) (SecT s1) (SecT s2)
            let cont2 = do
                tcCstrM_ l $ Unifies (loc x2) (loc e1)
                tcCstrM_ l $ Assigns (IdxT $ varExpr x2) (IdxT e1)
            let choice2 = (match2,cont2)
            choiceDec <- mkChoiceDec l e1 x2
            resolveMultipleSubstitutions l Nothing [SecT s1] ([choice1,choice2] ++ choiceDec)
    coercesSec'' opts st s1 s2 = constraintError (\x y mb -> Halt $ CoercionException "security type" x y mb) l e1 ppExprTy x2 ppVarTy Nothing

--classifiesCstrs :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> SecType -> TcM m ([TCstr],Set VarIdentifier)
--classifiesCstrs l e1 ct1 x2 s2 = do
--    st <- getCstrState
--    let ct2 = setCSec ct1 s2
--    dec@(DVar dv) <- newDecVar False Nothing
--    let classify' = ProcedureName (DecT dec) $ mkVarId "classify"
--    ppe1 <- pp e1
--    --v1@(VarName _ (VIden vn1)) <- newTypedVar "cl" (loc e1) False $ Just $ ppe1
--    let k1 = TcK (PDec False Nothing (PIden $ procedureNameId classify') Nothing [(False,Left e1,False)] (ComplexT ct2) dec) st
--    let k2 = TcK (Unifies (loc x2) (ComplexT ct2)) st
--    let k3 = TcK (Assigns (IdxT $ varExpr x2) (IdxT $ ProcCallExpr (ComplexT ct2) (bimap PIden id classify') Nothing [(e1,False)])) st
--    return ([k1,k2,k3],Set.fromList [dv])

--repeatsCstrs :: (ProverK loc m) => loc -> Expr -> ComplexType -> Var -> Expr -> TcM m ([TCstr],Set VarIdentifier)
--repeatsCstrs l e1 ct1 x2 d2 = do
--    st <- getCstrState
--    let ct2 = setCBase ct1 d2
--    dec@(DVar dv) <- newDecVar False Nothing
--    let repeat' = ProcedureName (DecT dec) $ mkVarId "repeat"
--    ppe1 <- pp e1
--    --v1@(VarName _ (VIden vn1)) <- newTypedVar "rp" (loc e1) False $ Just $ ppe1
--    let k1 = TcK (PDec False Nothing (PIden $ procedureNameId repeat') Nothing [(False,Left e1,False)] (ComplexT ct2) dec) st
--    let k2 = TcK (Unifies (loc x2) (ComplexT ct2)) st
--    let k3 = TcK (Assigns (IdxT $ varExpr x2) (IdxT $ ProcCallExpr (ComplexT ct2) (bimap PIden id repeat') Nothing [(e1,False)])) st
--    return ([k1,k2,k3],Set.fromList [dv])

coercesLit :: (ProverK loc m) => loc -> Expr -> TcM m ()
coercesLit l e@(LitPExpr t lit) = do
    b <- typeToBaseType l t
    coercesLitBase l (funit lit) b
--coercesLit l (ArrayConstructorPExpr (ComplexT ct@(CType s t d)) es) = do
--    -- coerce each element
--    let et = ComplexT $ CType s t $ indexExpr 0
--    --xs <- forM (zip [1..] es) $ \(i,e) -> pp e >>= \ppe -> newTypedVar ("ael"++show i) et False $ Just $ ppe
--    tcCoercesN l False es et
--    -- match the array's dimension
--    tcCstrM_ l $ Unifies (IdxT d) (IdxT $ indexExpr 1) -- dimension 1
--coercesLit l (MultisetConstructorPExpr (ComplexT ct@(CType s (MSet b) d)) es) = do
--    -- coerce each element
--    let et = ComplexT $ CType s b $ indexExpr 0
--    --xs <- forM (zip [1..] es) $ \(i,e) -> pp e >>= \ppe -> newTypedVar ("mel"++show i) et False $ Just $ ppe
--    tcCoercesN l False es et
--    -- match the array's dimension
--    tcCstrM_ l $ Unifies (IdxT d) (IdxT $ indexExpr 0) -- dimension 0
coercesLit l e = constraintError (CoercionException "literal") l e pp (loc e) pp Nothing  

equalsLit :: (ProverK loc m) => loc -> Literal () -> Literal () -> TcM m ()
equalsLit l lit1 lit2 | lit1 == lit2 = return ()
equalsLit l (IntLit _ i1) (IntLit _ i2) | i1 == i2 = return ()
equalsLit l (IntLit _ i1) (FloatLit _ f2) | fromInteger i1 == f2 = return ()
equalsLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
equalsLit l (FloatLit _ f1) (FloatLit _ f2) | f1 == f2 = return ()
equalsLit l lit1 lit2 = constraintError (EqualityException "literal type") l lit1 pp lit2 pp Nothing  

-- coerces a literal into a base type

--readable1 :: (ToVariable x var,ProverK loc m) => (x -> TcM m b) -> loc -> x -> TcM m b

coercesLitBase :: (ProverK loc m) => loc -> Literal () -> BaseType -> TcM m ()
coercesLitBase l (BoolLit _ b) t = tcCstrM_ l $ Unifies (BaseT t) (BaseT bool)
coercesLitBase l (StringLit _ s) t = tcCstrM_ l $ Unifies (BaseT t) (BaseT string)
coercesLitBase l lit@(IntLit _ i) t = readable1 coercesLitInt l t
    where
    coercesLitInt (TyPrim (t@(primIntBounds -> Just (min,max)))) = do
        unless (min <= i && i <= max) $ do
            ppt <- pp t
            tcWarn (locpos l) $ LiteralOutOfRange (show i) (ppt) (show min) (show max)
    coercesLitInt (TyPrim (t@(primFloatBounds -> Just (min,max)))) = do
        unless (min <= fromInteger i && fromInteger i <= max) $ do
            ppt <- pp t
            tcWarn (locpos l) $ LiteralOutOfRange (show i) (ppt) (show min) (show max)
    coercesLitInt t2@(TyPrim {}) = constraintError (\x y e -> CoercionException "literal base type" x y e) l lit pp t2 pp Nothing
    coercesLitInt t2@(BVar v@(varIdWrite -> True) c2) = do
        constraintError (\x y e -> Halt $ CoercionException "literal base type" x y e) l lit pp t2 pp Nothing
    coercesLitInt t2 = constraintError (\x y mb -> Halt $ CoercionException "literal base type" x y mb) l lit pp t2 pp Nothing  
coercesLitBase l lit@(FloatLit _ f) t = readable1 coercesLitFloat l t
    where
    coercesLitFloat (TyPrim (t@(primFloatBounds -> Just (min,max)))) | isPrimFloat t = do
        unless (min <= f && f <= max) $ do
            ppt <- pp t
            tcWarn (locpos l) $ LiteralOutOfRange (show f) (ppt) (show min) (show max)
    coercesLitFloat t2@(TyPrim {}) = constraintError (\x y e -> CoercionException "literal base type" x y e) l lit pp t2 pp Nothing
    coercesLitFloat t2@(BVar v@(varIdWrite -> True) c2) = do
        constraintError (\x y e -> Halt $ CoercionException "literal base type" x y e) l lit pp t2 pp Nothing
    coercesLitFloat t2 = constraintError (\x y mb -> Halt $ CoercionException "literal base type" x y mb) l lit pp t2 pp Nothing  
coercesLitBase l lit t2 = constraintError (\x y mb -> Halt $ CoercionException "literal base type" x y mb) l lit pp t2 pp Nothing  

decToken :: MonadIO m => TcM m DecType
decToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "dtok" mn (Just i) False False Nothing
    return $ DVar v

kindToken :: MonadIO m => Maybe KindClass -> TcM m KindType
kindToken cl = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "ktok" mn (Just i) False False Nothing
    return $ KVar v cl

secToken :: MonadIO m => KindType -> TcM m SecType
secToken k = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "stok" mn (Just i) False False Nothing
    return $ SVar v k
    
baseToken :: MonadIO m => Maybe DataClass -> TcM m BaseType
baseToken cl = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "btok" mn (Just i) False False Nothing
    return $ BVar v cl

arrayToken :: MonadIO m => Type -> Expr -> TcM m VArrayType
arrayToken b sz = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "atok" mn (Just i) False False Nothing
    return $ VAVar v b sz

complexToken :: MonadIO m => TcM m ComplexType
complexToken = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "ctok" mn (Just i) False False Nothing
    return $ CVar v False

exprToken :: MonadIO m => Type -> TcM m Expr
exprToken t = do
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "etok" mn (Just i) False False Nothing
    return $ RVariablePExpr t (VarName t $ VIden v)

sizeToken :: MonadIO m => TcM m Expr
sizeToken = do
    let t = BaseT index
    i <- liftIO newTyVarId
    mn <- State.gets (fst . moduleCount)
    let v = VarIdentifier "sztok" mn (Just i) False False Nothing
    return $ RVariablePExpr t (VarName t $ VIden v)

exprTypeToken :: MonadIO m => TcM m Expr
exprTypeToken = complexToken >>= exprToken . ComplexT

-- | Checks if a type is more specific than another, performing substitutions
compares :: (ProverK loc m) => loc -> Bool -> Type -> Type -> TcM m (Comparison (TcM m))
compares l isLattice (IdxT e1) (IdxT e2) = comparesExpr l isLattice e1 e2
compares l isLattice (BaseT b1) (BaseT b2) = do
    comparesBase l isLattice b1 b2
compares l isLattice (ComplexT c1) (ComplexT c2) = do
    comparesComplex l isLattice c1 c2
compares l isLattice (BaseT b1) (ComplexT c2) = do
    comparesComplex l isLattice (defCType b1) c2
compares l isLattice (ComplexT c1) (BaseT b2) = do
    comparesComplex l isLattice c1 (defCType b2)
compares l isLattice (SecT s1) (SecT s2) = do
    comparesSec l isLattice s1 s2
compares l isLattice (KindT k1) (KindT k2) = do
    comparesKind l isLattice k1 k2
compares l isLattice (SysT t1) (SysT t2) = do
    comparesSys l isLattice t1 t2
compares l isLattice (DecT d1) (DecT d2) = do
    comparesDec l d1 d2
compares l isLattice (VArrayT a1) (VArrayT a2) = do
    comparesArray l isLattice a1 a2
compares l isLattice (VAType b1 sz1) (VAType b2 sz2) = do
    o1 <- compares l isLattice b1 b2
    o2 <- compares l isLattice (IdxT sz1) (IdxT sz2)
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
compares l isLattice t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (ComparisonException "type") (pp1) (pp2) . Just)
        (equals l t1 t2 >> return (Comparison t1 t2 EQ EQ False))

comparesDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m (Comparison (TcM m))
comparesDec l = readable2 comparesDec' l
    where
    comparesDec' t1@(getReadableVar -> Just v1) t2@(getReadableVar -> Just v2) = do
        x <- decToken
        addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t1) $ DecT x
        addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t2) $ DecT x
        return (Comparison t1 t2 EQ EQ False)      
    comparesDec' t1 t2@(getReadableVar -> Just v1) = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t2) $ DecT t1
        return (Comparison t1 t2 LT EQ False)
    comparesDec' t1@(getReadableVar -> Just v2) t2 = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ DecT t1) $ DecT t2
        return (Comparison t1 t2 GT EQ False)
    comparesDec' t1 t2 = do
        pp1 <- pp t1
        pp2 <- pp t2
        addErrorM l
            (TypecheckerError (locpos l) . (ComparisonException "declaration type") (pp1) (pp2) . Just)
            (equalsDec l t1 t2 >> return (Comparison t1 t2 EQ EQ False))

comparesArray :: (ProverK loc m) => loc -> Bool -> VArrayType -> VArrayType -> TcM m (Comparison (TcM m))
comparesArray l isLattice = readable2 comparesArray' l
    where
    comparesArray' a1@(VAVal ts1 _) a2@(VAVal ts2 _) = do
        comparesList l isLattice ts1 ts2
    comparesArray' a1@(VAVar v1 b1 sz1) a2@(VAVar v2 b2 sz2) | v1 == v2 = return (Comparison a1 a2 EQ EQ False)
    comparesArray' a1@(getReadableVar -> Just (v1,b1,sz1)) a2@(getReadableVar -> Just (v2,b2,sz2)) = do
        x <- arrayToken b1 sz1
        addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a1) $ VArrayT x
        addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a2) $ VArrayT x
        return $ Comparison a1 a2 EQ EQ False 
    comparesArray' a1 a2@(getReadableVar -> Just (v2,b2,sz2)) = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a2) $ VArrayT a2
        return $ Comparison a1 a2 LT EQ False
    comparesArray' a1@(getReadableVar -> Just (v1,b1,sz1)) a2 = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ VArrayT a1) $ VArrayT a2
        return $ Comparison a1 a2 GT EQ False
    comparesArray' a1 a2 = constraintError (ComparisonException "array type") l a1 pp a2 pp Nothing

comparesSec :: (ProverK loc m) => loc -> Bool -> SecType -> SecType -> TcM m (Comparison (TcM m))
comparesSec l isLattice = readable2 (comparesSec' isLattice) l
    where
    comparesSec' isLattice t1@Public t2@Public = return (Comparison t1 t2 EQ EQ False)
    comparesSec' isLattice t1@(Private d1 k1) t2@(Private d2 k2) | d1 == d2 && k1 == k2 = do
        return (Comparison t1 t2 EQ EQ False)
    comparesSec' True t1@Public t2@(Private {}) = do
        ko <- hasAmbiguousTpltTokClass l DomainC
        return (Comparison t1 t2 EQ LT ko) -- public computations are preferrable (because of coercions)
    comparesSec' True t1@(Private {}) t2@Public = do
        ko <- hasAmbiguousTpltTokClass l DomainC
        return (Comparison t1 t2 EQ GT ko) -- public computations are preferrable (because of coercions)
    comparesSec' isLattice t1@(SVar v1 k1) t2@(SVar v2 k2) | v1 == v2 = do
        equalsKind l k1 k2
        return (Comparison t1 t2 EQ EQ False)
    comparesSec' isLattice t1@(getReadableVar -> Just (v1,k1)) t2@(getReadableVar -> Just (v2,k2)) = do
        (cmpk,ko) <- comparesKind l isLattice k1 k2 >>= compOrderingM l
        case cmpk of
            LT -> if isLattice then return $ Comparison t1 t2 EQ LT ko else return $ Comparison t1 t2 LT EQ False
            GT -> if isLattice then return $ Comparison t1 t2 EQ GT ko else return $ Comparison t1 t2 GT EQ False
            EQ -> do
                x <- secToken k1
                addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t1) $ SecT x
                addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t2) $ SecT x
                return $ Comparison t1 t2 EQ EQ False
    comparesSec' isLattice t1 t2@(getReadableVar -> Just (v2,k2)) = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t2) $ SecT t1
        if isLattice && not (isPrivateKind $ secTypeKind t1)
            then liftM (Comparison t1 t2 EQ LT) (hasAmbiguousTpltTokClass l DomainC)
            else return $ Comparison t1 t2 LT EQ False
    comparesSec' isLattice t1@(getReadableVar -> Just (v1,k1)) t2 = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ SecT t1) $ SecT t2
        if isLattice && not (isPrivateKind $ secTypeKind t2)
            then liftM (Comparison t1 t2 EQ GT) (hasAmbiguousTpltTokClass l DomainC)
            else return $ Comparison t1 t2 GT EQ False
    comparesSec' isLattice t1 t2 = constraintError (ComparisonException $ show isLattice ++ " security type") l t1 pp t2 pp Nothing

comparesKind :: (ProverK loc m) => loc -> Bool -> KindType -> KindType -> TcM m (Comparison (TcM m))
comparesKind l isLattice = readable2 (comparesKind' isLattice) l
    where
    comparesKind' isLattice t1@PublicK t2@PublicK = return (Comparison t1 t2 EQ EQ False)
    comparesKind' isLattice t1@(PrivateK k1) t2@(PrivateK k2) | k1 == k2 = return (Comparison t1 t2 EQ EQ False)
    comparesKind' True t1@PublicK t2@(PrivateK {}) = do
        ko <- hasAmbiguousTpltTokClass l KindC
        return (Comparison t1 t2 EQ LT ko) -- public computations are preferrable (because of coercions)
    comparesKind' True t1@(PrivateK {}) t2@PublicK = do
        ko <- hasAmbiguousTpltTokClass l KindC
        return (Comparison t1 t2 EQ GT ko) -- public computations are preferrable (because of coercions)
    comparesKind' isLattice t1@(KVar k1 priv1) t2@(KVar k2 priv2) | k1 == k2 = return (Comparison t1 t2 EQ EQ False)
    comparesKind' isLattice t1@(getReadableVar -> Just (v1,priv1)) t2@(getReadableVar -> Just (v2,priv2)) = do
        x <- kindToken (max priv1 priv2)
        addSubstM l (SubstMode CheckS False) (VarName (KType priv1) $ VIden v1) $ KindT x
        addSubstM l (SubstMode CheckS False) (VarName (KType priv2) $ VIden v2) $ KindT x
        let cmp = (compare priv2 priv1)
        if isLattice
            then liftM (Comparison t1 t2 EQ cmp) (hasAmbiguousTpltTokClass l KindC)
            else return $ Comparison t1 t2 cmp EQ False
    comparesKind' isLattice t1 t2@(getReadableVar -> Just (v2,priv2)) = do
        addSubstM l (SubstMode CheckS False) (VarName (KType priv2) $ VIden v2) $ KindT t1
        if isLattice && not (isPrivateKind t1)
            then liftM (Comparison t1 t2 EQ LT) (hasAmbiguousTpltTokClass l KindC)
            else return $ Comparison t1 t2 LT EQ False
    comparesKind' isLattice t1@(getReadableVar -> Just (v1,priv1)) t2 = do
        addSubstM l (SubstMode CheckS False) (VarName (KType priv1) $ VIden v1) $ KindT t2
        if isLattice && not (isPrivateKind t2)
            then liftM (Comparison t1 t2 EQ GT) (hasAmbiguousTpltTokClass l KindC)
            else return $ Comparison t1 t2 GT EQ False
    comparesKind' isLattice t1 t2 = constraintError (ComparisonException "kind type") l t1 pp t2 pp Nothing

comparesSys :: (ProverK loc m) => loc -> Bool -> SysType -> SysType -> TcM m (Comparison (TcM m))
comparesSys l isLattice (SysPush t1) (SysPush t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice (SysRet t1) (SysRet t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice (SysRef t1) (SysRef t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice (SysCRef t1) (SysCRef t2) = do
    compares l isLattice t1 t2
comparesSys l isLattice t1 t2 = constraintError (ComparisonException "syscall type") l t1 pp t2 pp Nothing

comparesBase :: (ProverK loc m) => loc -> Bool -> BaseType -> BaseType -> TcM m (Comparison (TcM m))
comparesBase l isLattice = readable2 (comparesBase' isLattice) l
    where
    comparesBase' isLattice t1@(TApp (TIden n1) ts1 d1) t2@(TApp (TIden n2) ts2 d2) = do
        equalsTIdentifier l (TIden n1) (TIden n2)
        comparesTpltArgs l isLattice ts1 ts2
        --comparesDec l d1 d2
    comparesBase' isLattice t1@(TyPrim p1) t2@(TyPrim p2) = equalsPrim l p1 p2 >> return (Comparison t1 t2 EQ EQ False)
    comparesBase' isLattice t1@(MSet b1) t2@(MSet b2) = comparesBase l isLattice b1 b2
    comparesBase' isLattice t1@(BVar v1 c1) t2@(BVar v2 c2) | v1 == v2 = return (Comparison t1 t2 EQ EQ False)
    comparesBase' isLattice t1@(getReadableVar -> Just (v1,c1)) t2@(getReadableVar -> Just (v2,c2)) = do
        x <- baseToken (max c1 c2)
        addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t1) $ BaseT x
        addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t2) $ BaseT x
        return $ Comparison t1 t2 (compare c2 c1) EQ False
    comparesBase' isLattice t1 t2@(getReadableVar -> Just (v2,c2)) = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t2) $ BaseT t1
        return $ Comparison t1 t2 LT EQ False
    comparesBase' isLattice t1@(getReadableVar -> Just (v1,c1)) t2 = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ BaseT t1) $ BaseT t2
        return $ Comparison t1 t2 GT EQ False
    comparesBase' isLattice t1 t2 = constraintError (ComparisonException "base type") l t1 pp t2 pp Nothing

comparesComplex :: (ProverK loc m) => loc -> Bool -> ComplexType -> ComplexType -> TcM m (Comparison (TcM m))
comparesComplex l isLattice = readable2 (comparesComplex' isLattice) l
    where
    comparesComplex' isLattice t1@Void t2@Void = return $ Comparison t1 t2 EQ EQ False
    comparesComplex' isLattice ct1@(CType s1 t1 d1) ct2@(CType s2 t2 d2) = do -- we don't compare sizes
        o1 <- comparesSec l isLattice s1 s2
        o2 <- comparesBase l isLattice t1 t2
        o3 <- comparesDim l isLattice d1 d2
        appendComparisons l [o1,o2,o3]
    comparesComplex' isLattice t1@(CVar v1 _) t2@(CVar v2 _) | v1 == v2 = return (Comparison t1 t2 EQ EQ False)
    comparesComplex' isLattice t1@(getReadableVar -> Just (v1,k1)) t2@(getReadableVar -> Just (v2,k2)) = do
        x <- complexToken
        addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t1) $ ComplexT x
        addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t2) $ ComplexT x
        debugTc $ do
            ppx <- ppr x
            pp1 <- ppr t1
            pp2 <- ppr t2
            liftIO $ putStrLn $ "comparesComplex token " ++ show ppx ++ " " ++ show pp1 ++ " " ++ show pp2
        return $ Comparison t1 t2 EQ EQ False  
    comparesComplex' isLattice t1 t2@(getReadableVar -> Just (v2,k2)) = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t2) $ ComplexT t1
        return $ Comparison t1 t2 LT EQ False
    comparesComplex' isLattice t1@(getReadableVar -> Just (v1,k1)) t2 = do
        addSubstM l (SubstMode CheckS False) (tyToVar $ ComplexT t1) $ ComplexT t2
        return $ Comparison t1 t2 GT EQ False
    comparesComplex' isLattice t1 t2 = constraintError (ComparisonException "complex type") l t1 pp t2 pp Nothing
    
comparesFoldable :: (ProverK loc m,Foldable t) => loc -> Bool -> t Type -> t Type -> TcM m (Comparison (TcM m))
comparesFoldable l isLattice xs ys = comparesList l isLattice (toList xs) (toList ys)

data Comparison m where
    Comparison :: VarsG m a => a -> a -> Ordering -> Ordering -> Bool -> Comparison m
  deriving (Typeable)
    
instance Typeable m => Data (Comparison m) where
    gfoldl k z (Comparison x y o1 o2 b) = z Comparison `k` x `k` y `k` o1 `k` o2 `k` b
    gunfold k z c = error "gunfold Comparison"
    toConstr (Comparison {}) = con_Comparison
    dataTypeOf _ = ty_Comparison

con_Comparison = mkConstr ty_Comparison "Comparison" [] Prefix
ty_Comparison   = mkDataType "Language.SecreC.TypeChecker.Constraint.Comparison" [con_Comparison]
    
instance Eq (Comparison m) where
    (Comparison x1 y1 o1 o3 b1) == (Comparison x2 y2 o2 o4 b2) = o1 == o2 && o3 == o4
instance Ord (Comparison m) where
    compare (Comparison _ _ o1 o3 b1) (Comparison _ _ o2 o4 b2) = compare o1 o2 `mappend` compare o3 o4
        
deriving instance Show (Comparison m)

instance Monad m => PP m (Comparison m) where
    pp (Comparison x y o1 o2 b) = do
        ppx <- pp x
        ppo1 <- pp o1
        ppo2 <- pp o2
        ppb <- pp b
        ppy <- pp y
        return $ ppx <+> ppo1 <+> ppo2 <+> ppb <+> ppy
instance (PP m VarIdentifier,MonadIO m,GenVar VarIdentifier m,Typeable m) => Vars GIdentifier m (Comparison m) where
    traverseVars f (Comparison x y o1 o2 b) = do
        x' <- f x
        y' <- f y
        o1' <- f o1
        o2' <- f o2
        b' <- f b
        return $ Comparison x' y' o1' o2' b'

compOrdering :: Comparison m -> (Ordering,Ordering,Bool)
compOrdering (Comparison _ _ o1 o2 b) = (o1,o2,b)
compOrderingM :: ProverK loc m => loc -> Comparison (TcM m) -> TcM m (Ordering,Bool)
compOrderingM l (Comparison _ _ o1 o2 b) = liftM (,b) (appendOrdering l o1 o2)
ppCompares x y o = ppid x <+> ppid o <+> ppid y

comparesList :: (ProverK loc m) => loc -> Bool -> [Type] -> [Type] -> TcM m (Comparison (TcM m))
comparesList l isLattice a@[] b@[] = return $ Comparison a b EQ EQ False
comparesList l isLattice a@(x:xs) b@(y:ys) = do
    f <- compares l isLattice x y
    g <- comparesList l isLattice xs ys
    appendComparison l f g
comparesList l isLattice xs ys = constraintError (ComparisonException "type") l xs pp ys pp Nothing
    
appendComparison :: (ProverK loc m) => loc -> Comparison (TcM m) -> Comparison (TcM m) -> TcM m (Comparison (TcM m))
appendComparison l c1@(Comparison x1 x2 EQ EQ b1) c2@(Comparison y1 y2 o3 o4 b2) = do
    return $ Comparison y1 y2 o3 o4 (b1 || b2)
appendComparison l c1@(Comparison x1 x2 o1 o2 b1) c2@(Comparison y1 y2 EQ EQ b2) = do
    return $ Comparison x1 x2 o1 o2 (b1 || b2)
appendComparison l c1@(Comparison x1 x2 o1 o2 b1) c2@(Comparison y1 y2 o3 o4 b2) = do
    o1' <- appendOrdering l o1 o3
    o2' <- appendOrdering l o2 o4
    appendOrdering l o1' o1'
    return $ Comparison (x1,y1) (x2,y2) o1' o2' (b1 || b2)

appendOrdering :: ProverK loc m => loc -> Ordering -> Ordering -> TcM m Ordering
appendOrdering l EQ y = return y
appendOrdering l x EQ = return x
appendOrdering l LT LT = return LT
appendOrdering l GT GT = return GT
appendOrdering l x y = constraintError (\x y mb -> Halt $ ComparisonException "comparison" x y mb) l x pp y pp Nothing

appendComparisons :: (ProverK loc m) => loc -> [Comparison (TcM m)] -> TcM m (Comparison (TcM m))
appendComparisons l xs = foldr0M (Comparison () () EQ EQ False) (appendComparison l) xs

assigns :: ProverK loc m => loc -> Type -> Type -> TcM m ()
assigns l (IdxT (RVariablePExpr _ v1)) (IdxT e2) = assignsExpr l v1 e2
assigns l (SecT (SVar v1 k1)) (SecT s2) = assignsSec l v1 k1 s2
assigns l (BaseT (BVar v1 c1)) (BaseT b2) = assignsBase l v1 c1 b2
assigns l (ComplexT (CVar v1 isNotVoid1)) (ComplexT ct2) = assignsComplex l v1 isNotVoid1 ct2
assigns l (ComplexT (CVar v1 isNotVoid1)) (BaseT b2) = assignsComplex l v1 isNotVoid1 (defCType b2)
assigns l (DecT (DVar v1)) (DecT d2) = assignsDec l v1 d2
assigns l (VArrayT (VAVar v1 b1 sz1)) (VArrayT a2) = assignsArray l v1 b1 sz1 a2
assigns l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    tcError (locpos l) $ UnificationException "type assignment" (pp1) (pp2) Nothing

unifiesN :: ProverK loc m => loc -> [Type] -> TcM m ()
unifiesN l ts = foldr0M_ (\t1 t2 -> tcCstrM_ l (Unifies t1 t2) >> return t2) ts

-- | Non-directed unification, without implicit security coercions.
-- applies substitutions
unifies :: (ProverK loc m) => loc -> Type -> Type -> TcM m ()
unifies l (BType c1) (BType c2) = return ()
unifies l (KType c1) (KType c2) = return ()
unifies l (KindT k1) (KindT k2) = unifiesKind l k1 k2
unifies l (IdxT e1) (IdxT e2) = unifiesExpr l e1 e2
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
    unifiesExprTy l sz1 sz2
--unifies l t1@(CondType t1' c1) t2@(CondType t2' c2) = do
--    unifies l t1' t2'
--    unifiesCondExpression l c1 c2
--unifies l t1@(CondType t1' c1) t2 = do
--    unifies l t1' t2
--    unifiesCondExpression l c1 trueExpr
--unifies l t1 t2@(CondType t2' c2) = do
--    unifies l t1 t2'
--    unifiesCondExpression l trueExpr c2
unifies l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "type") (pp1) (pp2) . Just)
        (equals l t1 t2)

assignsArray :: ProverK loc m => loc -> VarIdentifier -> Type -> Expr -> VArrayType -> TcM m ()
assignsArray l v1 b1 sz1 a2 = assignable bound ass err l (v1,b1,sz1)
    where
    bound a1' = tcCstrM_ l $ Unifies (VArrayT a1') (VArrayT a2)
    ass (v1,b1,sz1) = addSubstM l (SubstMode NoFailS True) (VarName (VAType b1 sz1) $ VIden v1) (VArrayT a2)
    err (v1,b1,sz1) = do
        pp2 <- pp a2
        pp1 <- pp v1
        genTcError (locpos l) $ text "cannot assign type" <+> pp2 <+> text "to non-writeable variable" <+> pp1

unifiesArray :: (ProverK loc m) => loc -> VArrayType -> VArrayType -> TcM m ()
unifiesArray l = readable2 unifiesArray' l
    where
    unifiesArray' (VAVal ts1 b1) (VAVal ts2 b2) = do
        unifiesList l ts1 ts2
        tcCstrM_ l $ Unifies b1 b2
    unifiesArray' a1@(getReadableVar -> Just (v1,b1,sz1)) a2@(getReadableVar -> Just (v2,b2,sz2)) | isWritable v1 == isWritable v2 = do
        o <- chooseWriteVar l v1 v2
        case o of
            GT -> addSubstM l (SubstMode CheckS True) (VarName (VAType b2 sz2) $ VIden v2) (VArrayT a1)
            otherwise -> addSubstM l (SubstMode CheckS True) (VarName (VAType b1 sz1) $ VIden v1) (VArrayT a2) 
    unifiesArray' a1@(getWritableVar -> Just (v1,b1,sz1)) a2 = do
        addSubstM l (SubstMode CheckS True) (VarName (VAType b1 sz1) $ VIden v1) (VArrayT a2)
    unifiesArray' a1 a2@(getWritableVar -> Just (v2,b2,sz2)) = do
        addSubstM l (SubstMode CheckS True) (VarName (VAType b2 sz2) $ VIden v2) (VArrayT a1)
    unifiesArray' a1 a2 = do
        pp1 <- pp a1
        pp2 <- pp a2
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "array") (pp1) (pp2) . Just)
            (equalsArray l a1 a2)

assignsDec :: ProverK loc m => loc -> VarIdentifier -> DecType -> TcM m ()
assignsDec l v1 d2 = assignable bound ass err l v1
    where
    bound d1' = tcCstrM_ l $ Unifies (DecT d1') (DecT d2)
    ass v1 = addSubstM l (SubstMode NoFailS True) (VarName DType $ VIden v1) (DecT d2)
    err v1 = do
        pp2 <- pp d2
        pp1 <- pp v1
        genTcError (locpos l) $ text "cannot assign type" <+> pp2 <+> text "to non-writeable variable" <+> pp1

unifiesDec :: (ProverK loc m) => loc -> DecType -> DecType -> TcM m ()
unifiesDec l d1 d2 = do
        pp1 <- pp d1
        pp2 <- pp d2
        addErrorM l (TypecheckerError (locpos l) . (UnificationException "declaration") (pp1) (pp2) . Just) $ readable2 unifiesDec' l d1 d2
  where
    unifiesDec' d1@(getReadableVar -> Just v1) d2@(getReadableVar -> Just v2) | isWritable v1 == isWritable v2 = do
        o <- chooseWriteVar l v1 v2
        case o of
            GT -> addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v2) (DecT d1)
            otherwise -> addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v1) (DecT d2)
    unifiesDec' d1@(getWritableVar -> Just v1) d2 = do
        addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v1) (DecT d2)
    unifiesDec' d1 d2@(getWritableVar -> Just v2) = do
        addSubstM l (SubstMode CheckS True) (VarName DType $ VIden v2) (DecT d1)
    unifiesDec' d1 d2 | isJust (decTypeTyVarId d1) && decTypeTyVarId d1 == decTypeTyVarId d2 = return ()
    unifiesDec' d1@(DecType i1 isRec1 _ _ _ tspecs1 _) d2@(DecType i2 isRec2 _ _ _ tspecs2 _) | isRec1 == isRec2 = do
        unifiesTpltArgs l tspecs1 tspecs2
    unifiesDec' t1 t2 = do
        pp1 <- pp t1
        pp2 <- pp t2
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "declaration type") (pp1) (pp2) . Just)
            (equalsDec l t1 t2)

assignsComplex :: ProverK loc m => loc -> VarIdentifier -> Bool -> ComplexType -> TcM m ()
assignsComplex l v1 isNotVoid1 d2 = assignable bound ass err l (v1,isNotVoid1)
    where
    bound d1' = tcCstrM_ l $ Unifies (ComplexT d1') (ComplexT d2)
    ass (v1,isNotVoid1) = addSubstM l (SubstMode NoFailS True) (VarName (TType $ isNotVoid1) $ VIden v1) (ComplexT d2)    
    err (v1,isNotVoid1) = do
        pp2 <- pp d2
        pp1 <- pp v1
        genTcError (locpos l) $ text "cannot assign type" <+> pp2 <+> text "to non-writeable variable" <+> pp1

unifiesComplex :: (ProverK loc m) => loc -> ComplexType -> ComplexType -> TcM m ()
unifiesComplex l = readable2 unifiesComplex' l
    where
    unifiesComplex' Void Void = return ()
    unifiesComplex' ct1@(CType s1 t1 d1) ct2@(CType s2 t2 d2) = do
        pp1 <- pp ct1
        pp2 <- pp ct2
        addErrorM l (TypecheckerError (locpos l) . (UnificationException "complex") (pp1) (pp2) . Just) $ do
            tcCstrM_ l $ Unifies (SecT s1) (SecT s2)
            tcCstrM_ l $ Unifies (BaseT t1) (BaseT t2)
            unifiesExprTy l d1 d2
    unifiesComplex' d1@(getReadableVar -> Just (v1,isNotVoid1)) d2@(getReadableVar -> Just (v2,isNotVoid2)) | isWritable v1 == isWritable v2 = do
        o <- chooseWriteVar l v1 v2
        case o of
            GT -> addSubstM l (SubstMode CheckS True) (VarName (TType $ max isNotVoid1 isNotVoid2) $ VIden v2) (ComplexT d1)
            otherwise -> addSubstM l (SubstMode CheckS True) (VarName (TType $ max isNotVoid1 isNotVoid2) $ VIden v1) (ComplexT d2)
    unifiesComplex' (getWritableVar -> Just (v1,isNotVoid1)) c2 = do
        (isNotVoid,c2') <- matchComplexClass l isNotVoid1 c2
        addSubstM l (SubstMode CheckS True) (VarName (TType isNotVoid) $ VIden v1) (ComplexT c2')
    unifiesComplex' c1 (getWritableVar -> Just (v2,isNotVoid2)) = do
        (isNotVoid,c1') <- matchComplexClass l isNotVoid2 c1
        addSubstM l (SubstMode CheckS True) (VarName (TType isNotVoid) $ VIden v2) (ComplexT c1')
    unifiesComplex' t1 t2 = do
        pp1 <- pp t1
        pp2 <- pp t2
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "complex type") (pp1) (pp2) . Just)
            (equalsComplex l t1 t2)

matchComplexClass :: ProverK loc m => loc -> Bool -> ComplexType -> TcM m (Bool,ComplexType)
matchComplexClass l False Void = return (False,Void)
matchComplexClass l isNotVoid c@(CType {}) = return (True,c)
matchComplexClass l isNotVoid (CVar v@(varIdRead -> True) k) = do
    mb <- tryResolveCVar l v k
    case mb of
        Just c' -> matchComplexClass l isNotVoid c'
        Nothing -> do
            let isNotVoid' = max isNotVoid k -- choose the most specific class
            return (isNotVoid',CVar v isNotVoid')
matchComplexClass l isNotVoid c@(CVar v@(varIdWrite -> False) k) | k >= isNotVoid = return (k,c)
matchComplexClass l isNotVoid c = do
    ppis <- pp isNotVoid
    ppc <- pp c
    genTcError (locpos l) $ text "complex kind mismatch" <+> ppis <+> text "against" <+> ppc
    

unifiesSec :: (ProverK loc m) => loc -> SecType -> SecType -> TcM m ()
unifiesSec l = readable2 unifiesSec' l
    where
    unifiesSec' Public Public = return ()
    unifiesSec' (Private d1 k1) (Private d2 k2) | d1 == d2 && k1 == k2 = do
        return ()
    unifiesSec' d1@(getReadableVar -> Just (v1,k1)) d2@(getReadableVar -> Just (v2,k2)) | isWritable v1 == isWritable v2 = do
        o <- chooseWriteVar l v1 v2
        case o of
            LT -> addSVarSubstM l CheckS (v1,k1) d2
            GT -> addSVarSubstM l CheckS (v2,k2) d1
            EQ -> addSVarSubstM l CheckS (v1,k1) d2 
    unifiesSec' (getWritableVar -> Just (v1,k1)) s2 = do
        (k,s2') <- matchSecClass l k1 s2
        addSVarSubstM l CheckS (v1,k) s2'
    unifiesSec' s1 (getWritableVar -> Just (v2,k2)) = do
        (k,s1') <- matchSecClass l k2 s1
        addSVarSubstM l CheckS (v2,k) s1'
    unifiesSec' t1 t2 = do
        pp1 <- pp t1
        pp2 <- pp t2
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "security type") (pp1) (pp2) . Just)
            (equalsSec l t1 t2)

addSVarSubstM l mode (v,k) s = addSubstM l (SubstMode mode True) (VarName (KindT k) $ VIden v) (SecT s)

matchSecClass :: ProverK loc m => loc -> KindType -> SecType -> TcM m (KindType,SecType)
matchSecClass l k Public = do
    unifiesKind l k PublicK
    return (k,Public)
matchSecClass l k s2@(Private _ k2) = do
    unifiesKind l k (PrivateK k2)
    return (k,s2)
matchSecClass l k s2@(SVar v2 k2) = do
    unifiesKind l k k2
    return (k2,s2)
matchSecClass l k s = do
    ppk <- pp k
    pps <- pp s
    genTcError (locpos l) $ text "security kind mismatch" <+> ppk <+> text "against" <+> pps

unifiesKind :: ProverK loc m => loc -> KindType -> KindType -> TcM m ()
unifiesKind l = readable2 unifiesKind' l
    where
    unifiesKind' PublicK PublicK = return ()
    unifiesKind' (PrivateK k1) (PrivateK k2) | k1 == k2 = return ()
    unifiesKind' k1@(getReadableVar -> Just (v1,priv1)) k2@(getReadableVar -> Just (v2,priv2)) | isWritable v1 == isWritable v2 = do
        let priv = max priv1 priv2
        case compare priv1 priv2 of
            LT -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v1) (KindT k2)
            GT -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v2) (KindT k1)
            EQ -> do
                o <- chooseWriteVar l v1 v2
                case o of
                    GT -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v2) (KindT k1)
                    otherwise -> addSubstM l (SubstMode CheckS True) (VarName (KType priv) $ VIden v1) (KindT k2)
    unifiesKind' (getWritableVar -> Just (v1,priv1)) k2 = do
        (priv1',k2') <- matchKindClass l priv1 k2
        addSubstM l (SubstMode CheckS True) (VarName (KType priv1') $ VIden v1) (KindT k2')
    unifiesKind' k1 (getWritableVar -> Just (v2,priv2)) = do
        (priv2',k1') <- matchKindClass l priv2 k1
        addSubstM l (SubstMode CheckS True) (VarName (KType priv2') $ VIden v2) (KindT k1')
    unifiesKind' t1 t2 = do
        pp1 <- pp t1
        pp2 <- pp t2
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "kind type") (pp1) (pp2) . Just)
            (equalsKind l t1 t2)

matchKindClass :: ProverK loc m => loc -> Maybe KindClass -> KindType -> TcM m (Maybe KindClass,KindType)
matchKindClass l Nothing t@PublicK = return (Nothing,t) -- no class for publics
matchKindClass l c t@(PrivateK k) = return (c,t) -- only class available is nonpublic
matchKindClass l c t@(KVar v@(varIdRead -> True) k) = do
    mb <- tryResolveKVar l v k
    case mb of
        Just k' -> matchKindClass l c k'
        Nothing -> do
            let k' = max c k -- choose the most specific class
            return (k',KVar v k')
matchKindClass l c t@(KVar v@(varIdWrite -> False) k) | k >= c = return (k,t)
matchKindClass l c k = do
    ppc <- pp c
    ppk <- pp k
    genTcError (locpos l) $ text "kind mismatch" <+> ppc <+> text "against" <+> ppk

assignsSec :: ProverK loc m => loc -> VarIdentifier -> KindType -> SecType -> TcM m ()
assignsSec l v1 k1 s2 = assignable bound ass err l (v1,k1)
    where
    bound s1' = tcCstrM_ l $ Unifies (SecT s1') (SecT s2)
    ass vk1 = addSVarSubstM l NoFailS vk1 s2
    err (v1,k1) = do
    pp2 <- pp s2
    pp1 <- pp k1
    genTcError (locpos l) $ text "cannot assign type" <+> pp2 <+> text "to non-writeable variable" <+> pp1

unifiesSys :: (ProverK loc m) => loc -> SysType -> SysType -> TcM m ()
unifiesSys l (SysPush t1) (SysPush t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRet t1) (SysRet t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysRef t1) (SysRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l (SysCRef t1) (SysCRef t2) = do
    tcCstrM_ l $ Unifies t1 t2
unifiesSys l t1 t2 = do
    pp1 <- pp t1
    pp2 <- pp t2
    addErrorM l
        (TypecheckerError (locpos l) . (UnificationException "system type") (pp1) (pp2) . Just)
        (equalsSys l t1 t2)

assignsBase :: ProverK loc m => loc -> VarIdentifier -> Maybe DataClass -> BaseType -> TcM m ()
assignsBase l v1 c1 d2 = assignable bound ass err l (v1,c1)
    where
    bound d1' = tcCstrM_ l $ Unifies (BaseT d1') (BaseT d2)
    ass (v1,c1) = addSubstM l (SubstMode NoFailS True) (VarName (BType c1) $ VIden v1) (BaseT d2)
    err (v1,c1) = do
    pp2 <- pp d2
    pp1 <- pp v1
    genTcError (locpos l) $ text "cannot assign type" <+> pp2 <+> text "to non-writeable variable" <+> pp1

unifiesBase :: (ProverK loc m) => loc -> BaseType -> BaseType -> TcM m ()
unifiesBase l = readable2 unifiesBase' l
    where
    unifiesBase' (TyPrim p1) (TyPrim p2) = equalsPrim l p1 p2
    unifiesBase' (MSet b1) (MSet b2) = unifiesBase l b1 b2
    unifiesBase' d1@(getReadableVar -> Just (v1,c1)) d2@(getReadableVar -> Just (v2,c2)) | isWritable v1 == isWritable v2 = do
        let c = max c1 c2
        case compare c1 c2 of
            LT -> addSubstM l (SubstMode CheckS True) (VarName (BType c) $ VIden v1) (BaseT d2)
            GT -> addSubstM l (SubstMode CheckS True) (VarName (BType c) $ VIden v2) (BaseT d1)
            EQ -> do
                o <- chooseWriteVar l v1 v2
                case o of
                    GT -> addSubstM l (SubstMode CheckS True) (VarName (BType c) $ VIden v2) (BaseT d1)
                    otherwise -> addSubstM l (SubstMode CheckS True) (VarName (BType c) $ VIden v1) (BaseT d2)
    unifiesBase' (getWritableVar -> Just (v1,c1)) t2 = do
        (c1',t2') <- matchDataClass l c1 t2
        addSubstM l (SubstMode CheckS True) (VarName (BType c1') $ VIden v1) (BaseT t2')
    unifiesBase' t1 (getWritableVar -> Just (v2,c2)) = do
        (c2',t1') <- matchDataClass l c2 t1
        addSubstM l (SubstMode CheckS True) (VarName (BType c2') $ VIden v2) (BaseT t1')
    unifiesBase' (TApp (TIden n1) ts1 d1) (TApp (TIden n2) ts2 d2) = do
        unifiesTIdentifier l (TIden n1) (TIden n2)
        unifiesTpltArgs l ts1 ts2
        --unifiesDec l d1 d2
    unifiesBase' t1 t2 = do
        pp1 <- pp t1
        pp2 <- pp t2
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "base type") (pp1) (pp2) . Just)
            (equalsBase l t1 t2)

matchDataClass :: ProverK loc m => loc -> Maybe DataClass -> BaseType -> TcM m (Maybe DataClass,BaseType)
matchDataClass l Nothing b = return (Nothing,b)
matchDataClass l (Just NumericClass) b@(TyPrim p) | isNumericPrimType p = return (Just NumericClass,b)
matchDataClass l (Just PrimitiveClass) b@(TyPrim p) = return (Just PrimitiveClass,b)
matchDataClass l c (BVar v@(varIdRead -> True) k) = do
    mb <- tryResolveBVar l v k
    case mb of
        Nothing -> do
            let k' = max c k
            return (k',BVar v k')
        Just b' -> matchDataClass l c b'
matchDataClass l c (BVar v k) = do
    let k' = max c k
    return (k',BVar v k')
matchDataClass l c b = do
    ppc <- pp c
    ppb <- pp b
    genTcError (locpos l) $ text "data type mismatch" <+> ppc <+> text "against" <+> ppb

unifiesTpltArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m ()
unifiesTpltArgs l ts1 ts2 = do
    matchTpltArgs l UnificationException (\x y -> tcCstrM_ l $ Unifies x y) ts1 ts2
    return ()

equalsTpltArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m ()
equalsTpltArgs l ts1 ts2 = do
    matchTpltArgs l EqualityException (\x y -> tcCstrM_ l $ Equals x y) ts1 ts2
    return ()

matchTpltArgs :: (ProverK loc m) => loc -> (String -> Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> (Type -> Type -> TcM m r) -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m [r]
matchTpltArgs l ex match ts1 ts2 = do
    pp1 <- pp ts1
    pp2 <- pp ts2
    addErrorM l (TypecheckerError (locpos l) . (ex "template arguments") (pp1) (pp2) . Just) $ matchTpltArgs' ts1 ts2
  where
    matchTpltArgs' ts1@(all (not . snd) -> True) [(t2,True)] = do
        let tt = tyOf t2
        b <- typeBase l tt
        r <- match t2 (VArrayT $ VAVal (map fst ts1) b)
        return [r]
    matchTpltArgs' [(t1,True)] ts2@(all (not . snd) -> True) = do
        let tt = tyOf t1
        b <- typeBase l tt
        r <- match t1 (VArrayT $ VAVal (map fst ts2) b)
        return [r]
    matchTpltArgs' [(t1,True)] [(t2,True)] = do
        r <- match t1 t2
        return [r]
    matchTpltArgs' ts1 ts2 = do
        ts1' <- concatMapM (expandVariadicType l) ts1
        ts2' <- concatMapM (expandVariadicType l) ts2
        constraintList (ex "template arguments") match l ts1' ts2'

--equalsSizes :: (ProverK loc m) => loc -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
--equalsSizes l szs1 szs2 = matchSizes l EqualityException (equalsExprTy l False) szs1 szs2
--
--unifiesSizes :: (ProverK loc m) => loc -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
--unifiesSizes l szs1 szs2 = matchSizes l UnificationException (unifiesExprTy l False) szs1 szs2

matchSizes :: (ProverK loc m) => loc -> (String -> Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> (Expr -> Expr -> TcM m ()) -> Maybe [(Expr,IsVariadic)] -> Maybe [(Expr,IsVariadic)] -> TcM m ()
matchSizes l ex match szs1 szs2 = do
    pp1 <- (ppOpt szs1 pp)
    pp2 <- (ppOpt szs2 pp)
    addErrorM l (TypecheckerError (locpos l) . (ex "sizes") pp1 pp2 . Just) $ matchSizes' szs1 szs2
  where
    matchSizes' (Just szs1@(all (not . snd) -> True)) (Just [(e2,True)]) = do
        match e2 (ArrayConstructorPExpr (loc e2) $ map fst szs1)
    matchSizes' (Just [(e1,True)]) (Just szs2@(all (not . snd) -> True)) = do
        match e1 (ArrayConstructorPExpr (loc e1) $ map fst szs2)
    matchSizes' (Just [(e1,True)]) (Just [(e2,True)]) = do
        match e1 e2
    matchSizes' (Just szs1) (Just szs2) = do
        szs1' <- concatMapM (expandVariadicExpr l False) szs1
        szs2' <- concatMapM (expandVariadicExpr l False) szs2
        constraintList (ex "sizes") match l szs1' szs2'
        return ()
    matchSizes' sz1 sz2 = return () -- ignore if both sizes are not known

expandVariadicExpr :: (ProverK loc m) => loc -> IsConst -> (Expr,IsVariadic) -> TcM m [Expr]
expandVariadicExpr = expandVariadicExpr' True
    where
    expandVariadicExpr' :: (ProverK loc m) => Bool -> loc -> IsConst -> (Expr,IsVariadic) -> TcM m [Expr]
    expandVariadicExpr' True l isConst (e@(RVariablePExpr t1 (VarName t2 (VIden v@(varIdRead -> True)))),isVariadic) = do
        mb <- tryResolveEVar l v t2
        case mb of
            Just e' -> expandVariadicExpr' True l isConst (fmap typed e',isVariadic)
            Nothing -> expandVariadicExpr' False l isConst (e,isVariadic)
    expandVariadicExpr' r l isConst (e,False) = case loc e of
        VAType {} -> do
            ppe <- pp e
            genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (ppe)
        VArrayT {} -> do
            ppe <- pp e
            genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (ppe)
        otherwise -> return [e]
    expandVariadicExpr' r l isConst (ArrayConstructorPExpr t es,True) = case t of
        VAType {} -> return es
        VArrayT {} -> return es
        otherwise -> do
            ppt <- pp t
            genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (ppt)
    expandVariadicExpr' r l isConst (e,True) = do
        let t = loc e
        case t of
            VAType b sz -> if isConst
                then do
                    sz' <- fullyEvaluateIndexExpr l sz
                    vs <- forM [0..pred (fromEnum sz')] $ \i -> newTypedVar ("vex"++show i) b False Nothing
                    let evs = map varExpr vs
                    tcCstrM_ l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t evs)
                    return evs
                else do
                    ArrayConstructorPExpr t' es' <- expandArrayExpr l e
                    return es'
            VArrayT a -> if isConst
                then do
                    ts <- expandVariadicType l (VArrayT a,True)
                    vs <- forM ts $ \t -> newTypedVar "vext" t False Nothing
                    let es = map varExpr vs
                    tcCstrM_ l $ Unifies (IdxT e) (IdxT $ ArrayConstructorPExpr t es)
                    return es
                else do
                    ArrayConstructorPExpr t' es' <- expandArrayExpr l e
                    return es'
            otherwise -> do
                ppt <- pp t
                genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (ppt)
    
expandVariadicType :: (ProverK loc m) => loc -> (Type,IsVariadic) -> TcM m [Type]
expandVariadicType l (t,False) = case tyOf t of
    VAType {} -> do
        ppt <- pp t
        genTcError (locpos l) $ text "Non-expanded variadic parameter pack" <+> quotes (ppt)
    otherwise -> return [t]
expandVariadicType l (VArrayT (VAVal ts _),True) = return ts
expandVariadicType l (t@(VArrayT a),True) = do
    let tt = tyOf t
    sz <- fullyEvaluateIndexExpr l =<< typeSize l tt
    b <- typeBase l tt
    vs <- forM [0..pred (fromEnum sz)] $ \i -> newVarOf ("varr"++show i) b False Nothing
    tcCstrM_ l $ Unifies t (VArrayT $ VAVal vs b)
    return vs
expandVariadicType l (t,True) = do
    ppt <- pp t
    genTcError (locpos l) $ text "Not a variadic parameter pack" <+> quotes (ppt)

unifiesList :: (ProverK loc m) => loc -> [Type] -> [Type] -> TcM m ()
unifiesList l [] [] = return ()
unifiesList l (x:xs) (y:ys) = do
    tcCstrM_ l $ Unifies x y
    unifiesList l xs ys
unifiesList l xs ys = constraintError (UnificationException "type") l xs pp ys pp Nothing

resolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> Bool -> TcM m ComplexType
resolveCVar l v isNotVoid = do
    mb <- tryResolveCVar l v isNotVoid
    case mb of
        Just t -> return t
        Nothing -> do
            ppv <- pp v
            tcError (locpos l) $ Halt $ UnresolvedVariable ppv

resolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> KindType -> TcM m SecType
resolveSVar l v c = do
    mb <- tryResolveSVar l v c
    case mb of
        Just t -> return t
        Nothing -> do
            ppv <- pp v
            tcError (locpos l) $ Halt $ UnresolvedVariable ppv

resolveKVar :: (ProverK loc m) => loc -> VarIdentifier -> Maybe KindClass -> TcM m KindType
resolveKVar l v c = do
    mb <- tryResolveKVar l v c
    case mb of
        Just t -> return t
        Nothing -> do
            ppv <- pp v
            tcError (locpos l) $ Halt $ UnresolvedVariable ppv

resolveVAVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> Expr -> TcM m VArrayType
resolveVAVar l v b sz = do
    mb <- tryResolveVAVar l v b sz
    case mb of
        Just t -> return t
        Nothing -> do
            ppv <- pp v
            tcError (locpos l) $ Halt $ UnresolvedVariable ppv

resolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m DecType
resolveDVar l v = resolveTVar l v >>= typeToDecType l

resolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> Maybe DataClass -> TcM m BaseType
resolveBVar l v c = do
    mb <- tryResolveBVar l v c
    case mb of
        Nothing -> do
            ppv <- pp v
            tcError (locpos l) $ Halt $ UnresolvedVariable (ppv)
        Just t -> return t

resolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m Type
resolveTVar l v = do
    mb <- tryResolveTVar l v
    case mb of
        Nothing -> do
            ppv <- pp v
            tcError (locpos l) $ Halt $ UnresolvedVariable (ppv)
        Just t -> return t

tryResolveSVar :: (ProverK loc m) => loc -> VarIdentifier -> KindType -> TcM m (Maybe SecType)
tryResolveSVar l v k = do
    mb <- tryResolveTVar l v >>= mapM (typeToSecType l)
    case mb of
        Nothing -> return Nothing
        Just s' -> do
            tcCstrM_ l $ Unifies (KindT k) (KindT $ secTypeKind s')
            return $ Just s'

tryResolveKVar :: (ProverK loc m) => loc -> VarIdentifier -> Maybe KindClass -> TcM m (Maybe KindType)
tryResolveKVar l v c = do
    mb <- tryResolveTVar l v >>= mapM (typeToKindType l)
    case mb of
        Nothing -> return Nothing
        Just k' -> liftM (Just . snd) $ matchKindClass l c k'

tryResolveVAVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> Expr -> TcM m (Maybe VArrayType)
tryResolveVAVar l v b sz = do
    mb <- tryResolveTVar l v >>= mapM (\t -> typeToVArrayType l t)
    case mb of
        Nothing -> return Nothing
        Just a' -> do
            tcCstrM_ l $ Unifies b (vArrayBase a')
            unifiesExprTy l sz (vArraySize a')
            return $ Just a'

tryResolveBVar :: (ProverK loc m) => loc -> VarIdentifier -> Maybe DataClass -> TcM m (Maybe BaseType)
tryResolveBVar l v k = do
    mb <- tryResolveTVar l v >>= mapM (typeToBaseType l)
    case mb of
        Nothing -> return Nothing
        Just b -> liftM (Just . snd) $ matchDataClass l k b

tryResolveCVar :: (ProverK loc m) => loc -> VarIdentifier -> Bool -> TcM m (Maybe ComplexType)
tryResolveCVar l v isNotVoid = do
    mb <- tryResolveTVar l v >>= mapM (typeToComplexType l)
    case mb of
        Nothing -> return Nothing
        Just c' -> case c' of
            CVar v' isNotVoid' -> return $ Just $ CVar v' (max isNotVoid isNotVoid')
            otherwise -> return $ Just c'

tryResolveDVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe DecType)
tryResolveDVar l v = tryResolveTVar l v >>= mapM (typeToDecType l)

-- | tries to resolve a type variable by looking its value in the substitutions and in the environment
tryResolveTVar :: (ProverK loc m) => loc -> VarIdentifier -> TcM m (Maybe Type)
tryResolveTVar l v | not (varIdRead v) = return Nothing
tryResolveTVar l v = do
--    liftIO $ putStrLn $ "resolvingTVar " ++ ppr v
    addGDependencies $ VIden v
    -- lookup in the substitution environment
    s <- getTSubsts l
    mb <- substsFromMap (Map.mapKeys VIden $ unTSubsts s) (VIden v::GIdentifier)
    case mb of
        Just t -> replaceSubstM l v t
        Nothing -> return ()
    return $ mb

-- | tries to resolve an expression
tryResolveEVar :: (ProverK loc m) => loc -> VarIdentifier -> Type -> TcM m (Maybe (Expression GIdentifier (Typed loc)))
tryResolveEVar l v t | not (varIdRead v) = return Nothing
tryResolveEVar l v t = do
--    liftIO $ putStrLn $ "resolvingEVar " ++ ppr v
    addGDependencies $ VIden v
    ss <- getTSubsts l
    mb <- case Map.lookup v (unTSubsts ss) of
        Just (IdxT e) -> do
            tcCstrM_ l $ Unifies t (loc e)
            return $ Just (fmap (Typed l) e)
        Just a@(VArrayT (VAVal (unIdxs -> Just es) _)) -> do
            tcCstrM_ l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ ArrayConstructorPExpr (tyOf a) es
        Just a@(VArrayT (VAVar v _ _)) -> do
            tcCstrM_ l $ Unifies t (tyOf a)
            return $ Just $ fmap (Typed l) $ RVariablePExpr (tyOf a) (VarName (tyOf a) $ VIden v)
        otherwise -> return Nothing
    case mb of
        Just e -> replaceSubstM l v (IdxT $ fmap typed e)
        Nothing -> return ()
    return mb

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

isSupportedPrint :: (ProverK loc m) => loc -> [(IsConst,Either Expr Type,IsVariadic)] -> [Var] -> TcM m ()
isSupportedPrint l es xs = forM_ (zip es xs) $ \(e,x) -> do
    (dec,[(_,y,_)]) <- pDecCstrM l Nothing False False True (PIden $ mkVarId "tostring") Nothing [e] (BaseT string)
    case y of
        Left ye -> assignsExprTy l x ye
        Right yt -> unifies l yt (loc x)
    return ()

--unifiesCondExpression :: (ProverK loc m) => loc -> Cond -> Cond -> TcM m ()
--unifiesCondExpression l e1 e2 = unifiesExprTy l False e1 e2 `mplus` satisfiesCondExpressions l [e1,e2]

--satisfiesCondExpressions :: (ProverK loc m) => loc -> [Cond] -> TcM m ()
--satisfiesCondExpressions l is = do
--    cs <- prove l "satisfiesCondExpressions" $ mapM (expr2SimpleIExpr . fmap (Typed l)) is
--    isValid l $ iAnd cs

assignsExpr :: ProverK loc m => loc -> Var -> Expr -> TcM m ()
assignsExpr l v1@(VarName t1 (VIden n1)) e2 = assignable bound ass err l (VarName t1 n1)
    where
    bound e1' = do
        pp2 <- pp e2
        pp1 <- pp v1
        pp1' <- pp e1'
        addErrorM l (TypecheckerError (locpos l) . GenTcError (text "cannot assign expression" <+> pp2 <+> text "to bound variable" <+> pp1 <+> text "=" <+> pp1') . Just) $
            tcCstrM_ l $ Unifies (IdxT e1') (IdxT e2)
    ass (VarName t1 n1) = addValueM l (SubstMode NoFailS True) (VarName t1 $ VIden n1) e2
    err v1 = do
        pp2 <- pp e2
        pp1 <- pp v1
        genTcError (locpos l) $ text "cannot assign expression" <+> pp2 <+> text "to non-writable variable" <+> pp1



unifiesExpr :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()
unifiesExpr l e1 e2 = do
        pp1 <- pp e1
        pp2 <- pp e2
        addErrorM l (TypecheckerError (locpos l) . (UnificationException "expression") (pp1) (pp2) . Just) $ readable2 (readable2List [tryInlineUnaryExpr l,tryProjectExpr l,tryVArraySizeExpr l,tryExpandArrayExpr l] unifiesExpr') l e1 e2
  where
    unifiesExpr' e1@(getReadableVar -> Just v1@(VarName t1 n1)) e2@(getReadableVar -> Just v2@(VarName t2 n2)) | isWritable v1 == isWritable v2 = do
        o <- chooseWriteVar l n1 n2
        case o of
            GT -> addValueM l (SubstMode CheckS True) (VarName t2 $ VIden n2) e1
            otherwise -> addValueM l (SubstMode CheckS True) (VarName t1 $ VIden n1) e2
    unifiesExpr' e1@(getWritableVar -> Just (VarName t1 n1)) e2 = do
        addValueM l (SubstMode CheckS True) (VarName t1 $ VIden n1) e2
    unifiesExpr' e1 e2@(getWritableVar -> Just (VarName t2 n2)) = do
        addValueM l (SubstMode CheckS True) (VarName t2 $ VIden n2) e1
    unifiesExpr' (ArrayConstructorPExpr t1 es1) (ArrayConstructorPExpr t2 es2) = do
        constraintList (UnificationException "expression") (unifiesExprTy l) l es1 es2
        return ()
    unifiesExpr' (UnaryExpr ret1 o1 e1) (UnaryExpr ret2 o2 e2) = do
        tcCstrM_ l $ Unifies ret1 ret2
        unifiesOp l o1 o2
        tcCstrM_ l $ Unifies (IdxT e1) (IdxT e2)
    unifiesExpr' e1 e2 = do
        (_,ks) <- tcWithCstrs l "unifiesExpr'" $ tcCstrM_ l $ Unifies (loc e1) (loc e2)
        withDeps LocalScope $ do
            addDeps "unifies" LocalScope ks
            tcCstrM_ l $ Equals (IdxT e1) (IdxT e2)

tryProjectExpr :: ProverK loc m => loc -> Expr -> TcM m (Maybe Expr)
tryProjectExpr l (PostIndexExpr t e s) = tryTcErrorMaybe l $ do
    arr' <- expandArrayExpr l e
    projectArrayExpr l arr' (Foldable.toList s)
tryProjectExpr l e = return Nothing

tryVArraySizeExpr :: ProverK loc m => loc -> Expr -> TcM m (Maybe Expr)
tryVArraySizeExpr l (VArraySizeExpr _ e) = tryTcErrorMaybe l $ typeSize l (loc e)
tryVArraySizeExpr l e = return Nothing

projectArrayExpr :: ProverK loc m => loc -> Expr -> [Index GIdentifier Type] -> TcM m Expr
projectArrayExpr l e [] = return e
projectArrayExpr l (ArrayConstructorPExpr t es) (IndexInt _ ie:s) = do
    i <- liftM fromEnum $ fullyEvaluateIndexExpr l ie
    checkIdx l i es
    projectArrayExpr l (es !! i) s
projectArrayExpr l (ArrayConstructorPExpr t es) (IndexSlice _ il iu:s) = do
    il' <- liftM fromEnum $ fullyEvaluateIndexExpr l $ maybe (indexExpr $ toEnum 0) id il
    iu' <- liftM fromEnum $ fullyEvaluateIndexExpr l $ maybe (indexExpr $ toEnum $ length es) id iu
    checkIdx l il' es
    checkIdx l iu' es
    projectArrayExpr l (ArrayConstructorPExpr (chgArraySize (length es) t) $ drop il' $ take iu' es) s

checkIdx :: ProverK loc m => loc -> Int -> [a] -> TcM m ()
checkIdx l i xs = unless (i >= 0 && i <= length xs) $ do
    genTcError (locpos l) $ text "failed to evaluate projection"

chgArraySize :: Int -> Type -> Type
chgArraySize sz (VAType b _) = VAType b (indexExpr $ toEnum sz)
chgArraySize sz (VArrayT (VAVar v t _)) = VArrayT $ VAVar v t (indexExpr $ toEnum sz)
chgArraySize sz t = t

expandArrayExpr :: ProverK loc m => loc -> Expr -> TcM m Expr
expandArrayExpr l e = do
    mb <- tryExpandArrayExpr l e
    case mb of
        Just e' -> return e'
        Nothing -> do
            ppe <- pp e
            genTcError (locpos l) $ text "cannot expand array expression" <+> quotes ppe

tryExpandArrayExpr :: ProverK loc m => loc -> Expr -> TcM m (Maybe Expr)
tryExpandArrayExpr l e@(ArrayConstructorPExpr {}) = return Nothing
tryExpandArrayExpr l e@(loc -> t) = tryTcErrorMaybe l $ do
    b <- typeBase l t
    dim <- typeDim l t
    ppe <- pp e
    idim <- prove l ("tryExpandArrayExpr " ++ show ppe) $ expr2SimpleIExpr $ fmap (Typed l) dim
    idim <- isValid l (IBinOp IEq idim $ ILit $ IUint64 1)
    sz <- typeSize l t
    nsz <- fullyEvaluateIndexExpr l sz
    es <- forM [0..pred (fromEnum nsz)] $ \i -> do
        let w = indexExpr $ toEnum i
        return $ PostIndexExpr b e $ WrapNe $ IndexInt (loc w) w
    let arr = ArrayConstructorPExpr t es
    case getWritableVar e of
        Just (VarName vt vn) -> addValueM l (SubstMode CheckS True) (VarName vt $ VIden vn) arr
        otherwise ->  return ()
    return arr

equalsTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()
equalsTIdentifier l (OIden (OpCast _ t1)) (OIden (OpCast _ t2)) = do
    equals l (castTypeToType t1) (castTypeToType t2)
equalsTIdentifier l (OIden op1) (OIden op2) | funit op1 == funit op2 = return ()
equalsTIdentifier l n1 n2 | n1 == n2 = return ()
equalsTIdentifier l t1 t2 = constraintError (UnificationException "identifier") l t1 pp t2 pp Nothing
    
unifiesTIdentifier :: (ProverK loc m) => loc -> TIdentifier -> TIdentifier -> TcM m ()
unifiesTIdentifier l (OIden (OpCast _ t1)) (OIden (OpCast _ t2)) = do
    unifies l (castTypeToType t1) (castTypeToType t2)
unifiesTIdentifier l (OIden op1) (OIden op2) | funit op1 == funit op2 = return ()
unifiesTIdentifier l n1 n2 | n1 == n2 = return ()
unifiesTIdentifier l t1 t2 = constraintError (UnificationException "identifier") l t1 pp t2 pp Nothing

equalsExpr :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()
equalsExpr l e1 e2 = do
--    (_,e1') <- simplifyNonVoidExpression True $ fmap (Typed l) e1
--    (_,e2') <- simplifyNonVoidExpression True $ fmap (Typed l) e2
    pp1 <- pp e1
    pp2 <- pp e2
    addErrorM l
        (TypecheckerError (locpos l) . (EqualityException "expression") (pp1) (pp2) . Just)
        (readable2 (readable2List [tryInlineUnaryExpr l,tryProjectExpr l,tryVArraySizeExpr l,tryExpandArrayExpr l] equalsExpr') l e1 e2)
  where
    equalsExpr' e1 e2 | e1 == e2 = return ()
    equalsExpr' (UnaryExpr ret1 o1 e1) (UnaryExpr ret2 o2 e2) = do
        tcCstrM_ l $ Equals ret1 ret2
        equalsOp l o1 o2
        tcCstrM_ l $ Equals (IdxT e1) (IdxT e2)
    equalsExpr' (LitPExpr t1 lit1) (LitPExpr t2 lit2) = do
        equalsLit l (funit lit1) (funit lit2)
        tcCstrM_ l $ Unifies t1 t2
    equalsExpr' e1 e2 = sameExpr e1 e2
    sameExpr e1 e2 = do
        pp1 <- ppr e1
        pp2 <- ppr e2
        i1 <- prove l ("equalsExpr1 " ++ pp1) $ expr2SimpleIExpr $ fmap (Typed l) e1
        i2 <- prove l ("equalsExpr2 " ++ pp2) $ expr2SimpleIExpr $ fmap (Typed l) e2
        unless (i1 == i2) $ isValid l (IBinOp (IEq) i1 i2)
--    equalsExpr' e1 e2 | not doStatic = do
--        eq <- eqExprs l False e1 e2
--        opts <- askOpts
--        when (checkAssertions opts) $ getDeps >>= \deps -> checkCstrM_ l deps $ CheckAssertion eq

--tryUnfoldUnaryExpr :: SimplifyK loc m => loc -> Expr -> TcM m (Maybe Expr)
--tryUnfoldUnaryExpr l ue = do
--    mb <- tryInlineUnaryExpr l ue
--    case mb of
--        Just e' -> return $ Just e'
--        Nothing -> tryRemoveUnaryExpr l ue
--tryUnfoldUnaryExpr l ue = return Nothing
--
--tryRemoveUnaryExpr :: ProverK loc m => loc -> Expr -> TcM m (Maybe Expr)
--tryRemoveUnaryExpr l ue@(UnaryExpr ret o e) = do
--    mb <- tryTcError $ equals l ret (loc e)
--    case mb of
--        Right _ -> return e
--        Left _ -> return Nothing
--tryRemoveUnaryExpr l e = return Nothing

equalsOp :: ProverK loc m => loc -> Op GIdentifier Type -> Op GIdentifier Type -> TcM m ()
equalsOp l o1 o2 | funit o1 == funit o2 = tcCstrM_ l $ Equals (loc o1) (loc o2)
equalsOp l o1 o2 = constraintError (EqualityException "operation") l o1 pp o2 pp Nothing

unifiesOp :: ProverK loc m => loc -> Op GIdentifier Type -> Op GIdentifier Type -> TcM m ()
unifiesOp l o1 o2 | funit o1 == funit o2 = tcCstrM_ l $ Unifies (loc o1) (loc o2)
unifiesOp l o1 o2 = constraintError (EqualityException "operation") l o1 pp o2 pp Nothing

comparesTpltArgs :: (ProverK loc m)
    => loc -> Bool -> [(Type,IsVariadic)] -> [(Type,IsVariadic)] -> TcM m (Comparison (TcM m))
comparesTpltArgs l isLattice ts1 ts2 = do
    os <- constraintList (ComparisonException "template arguments") comparesTpltArg l ts1 ts2
    appendComparisons l os
  where
    comparesTpltArg (t1,b1) (t2,b2) = do
        unless (b1 == b2) $ genTcError (locpos l) $ text "incomparable template arguments"
        compares l isLattice t1 t2

comparesDim :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
comparesDim l True e1 e2 = do
    mb1 <- isZeroIdxExpr l e1
    mb2 <- isZeroIdxExpr l e2
    ko <- hasAmbiguousTpltTok l $ \v -> typeClass "swap" (varNameToType v) == ExprC TypeC
    case (mb1,mb2) of
        (Right True,Right True) -> return (Comparison e1 e2 EQ EQ False)
        (Right False,Right False) -> return (Comparison e1 e2 EQ EQ False)
        (Right True,Right False) -> return (Comparison e1 e2 EQ LT ko)
        (Right False,Right True) -> return (Comparison e1 e2 EQ GT ko)
        (Right False,_) -> return (Comparison e1 e2 LT EQ False)
        (_,Right False) -> return (Comparison e1 e2 GT EQ False)
        otherwise -> comparesExpr l True e1 e2 >>= swapDimComp l
comparesDim l False e1 e2 = comparesExpr l False e1 e2
    
swapDimComp :: ProverK loc m => loc -> Comparison (TcM m) -> TcM m (Comparison (TcM m))
swapDimComp l (Comparison x y o1 o2 b) = do
    ko <- hasAmbiguousTpltTokClass l (ExprC TypeC)
    return $ Comparison x y o2 o1 (b || ko)
    
comparesExpr :: (ProverK loc m) => loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
comparesExpr l isLattice e1 e2 = do
    pp1 <- pp e1
    pp2 <- pp e2
    addErrorM l (TypecheckerError (locpos l) . (ComparisonException "expression") (pp1) (pp2) . Just) (readable2 (readable2List [tryInlineUnaryExpr l,tryProjectExpr l,tryVArraySizeExpr l,tryExpandArrayExpr l] comparesExpr') l e1 e2)
  where
--    comparesExpr' :: (ProverK loc m) => Bool -> Bool -> loc -> Bool -> Expr -> Expr -> TcM m (Comparison (TcM m))
    comparesExpr' e1 e2 | e1 == e2 = return (Comparison e1 e2 EQ EQ False)
    comparesExpr' e1@(getReadableVar -> Just (VarName t1 n1)) e2@(getReadableVar -> Just (VarName t2 n2)) = do
        cmp <- compares l isLattice t1 t2
        let t = case compOrdering cmp of
                        (o,isLat,_) -> if (mappend o isLat==GT) then t2 else t1
        x <- exprToken t
        addValueM l (SubstMode NoCheckS False) (VarName t1 $ VIden n1) x
        addValueM l (SubstMode NoCheckS False) (VarName t2 $ VIden n2) x
        return cmp
    comparesExpr' e1@(getReadableVar -> Just (VarName t1 n1)) e2 = do
        addValueM l (SubstMode NoCheckS False) (VarName t1 $ VIden n1) e2
        return (Comparison e1 e2 GT EQ False)
    comparesExpr' e1 e2@(getReadableVar -> Just (VarName t2 n2)) = do
        addValueM l (SubstMode NoCheckS False) (VarName t2 $ VIden n2) e1
        return (Comparison e1 e2 LT EQ False)
    comparesExpr' e1 e2 = do
        equalsExpr l e1 e2
        return (Comparison e1 e2 EQ EQ False)

equalsExprTy :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()
equalsExprTy l e1 e2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppExprTy e2)
    addErrorM l (TypecheckerError (locpos l) . (EqualityException "typed expression") pp1 pp2 . Just) $ do
        tcCstrM_ l $ Equals (IdxT e1) (IdxT e2)
        tcCstrM_ l $ Equals (loc e1) (loc e2)

unifiesExprTy :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()
unifiesExprTy l e1 e2 = do
    pp1 <- (ppExprTy e1)
    pp2 <- (ppExprTy e2)
    addErrorM l (TypecheckerError (locpos l) . (UnificationException "typed expression") pp1 pp2 . Just) $ do
        tcCstrM_ l $ Unifies (loc e1) (loc e2)
        tcCstrM_ l $ Unifies (IdxT e1) (IdxT e2)

assignsExprTys :: (ProverK loc m) => loc -> [(Expr,Var)] -> TcM m ()
assignsExprTys l exs = forM_ exs $ \(e,x) -> assignsExprTy l x e

assignsExprTy :: (ProverK loc m) => loc -> Var -> Expr -> TcM m ()
assignsExprTy l v1 e2 = do
    pp1 <- (ppExprTy v1)
    pp2 <- (ppExprTy e2)
    addErrorM l (TypecheckerError (locpos l) . (UnificationException "assign typed expression") pp1 pp2 . Just) $ do
        tcCstrM_ l $ Unifies (loc v1) (loc e2)
        tcCstrM_ l $ Assigns (IdxT $ varExpr v1) (IdxT e2)
    
constraintError :: (ProverK loc m,VarsG (TcM m) a,VarsG (TcM m) b) => (Doc -> Doc -> Maybe SecrecError -> TypecheckerErr) -> loc -> a -> (a -> TcM m Doc) -> b -> (b -> TcM m Doc) -> Maybe SecrecError -> TcM m res
constraintError k l e1 pp1 e2 pp2 (Just suberr) = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    p1 <- pp1 e1'
    p2 <- pp2 e2'
    tcError (locpos l) $ k p1 p2 $ Just suberr
constraintError k l e1 pp1 e2 pp2 Nothing = do
    e1' <- specializeM l e1
    e2' <- specializeM l e2
    p1 <- pp1 e1'
    p2 <- pp2 e2'
    tcError (locpos l) $ k p1 p2 Nothing

constraintList :: (ProverK loc m,VarsG (TcM m) [a],VarsG (TcM m) [b]) =>
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
    ic <- prove l "checkassertion" $ expr2SimpleIExpr $ fmap (Typed l) e
    isValid l ic
    
checkEqual :: (ProverK loc m) => loc -> Expr -> Expr -> TcM m ()
checkEqual l e1 e2 = do
    (i1,i2) <- prove l "checkequal" $ do
        i1 <- expr2SimpleIExpr $ fmap (Typed l) e1
        i2 <- expr2SimpleIExpr $ fmap (Typed l) e2
        return (i1,i2)
    isValid l $ IBinOp (IEq) i1 i2

checkIndex :: (ProverK loc m,SMTK loc) => loc -> Expr -> TcM m ()
checkIndex l e = do
    ie <- prove l "checkindex" $ expr2SimpleIExpr $ fmap (Typed l) e
    isValid l $ IBinOp (ILeq) (ILit $ IUint64 0) ie

pDecCstrM :: (ProverK loc m) => loc -> Maybe [EntryEnv] -> Bool -> Bool -> Bool -> PIdentifier -> (Maybe [(Type,IsVariadic)]) -> [(IsConst,Either Expr Type,IsVariadic)] -> Type -> TcM m (DecType,[(IsConst,Either Expr Type,IsVariadic)])
pDecCstrM l entries isTop isCtx doCoerce pid targs es tret = do
    dec <- newDecVar False Nothing
    opts <- askOpts
    st <- getCstrState
    if (doCoerce && checkCoercion (implicitCoercions opts) st)
        then do
            xs <- forM es $ coerceArg isTop
            tcTop_ l isTop $ PDec isCtx entries pid targs xs tret dec
            return (dec,xs)
        else do
            tcTop_ l isTop $ PDec isCtx entries pid targs es tret dec
            return (dec,es)
  where
    coerceArg isTop (isConst,Left e,isVariadic) = do
        tx <- newTyVar True False Nothing
        vtx <- mkVariadicTyArray isVariadic False tx
        ppe <- pp e
        x <- tcCoerces l isTop Nothing e vtx
        return (isConst,Left x,isVariadic)
    coerceArg isTop (isConst,Right t,isVariadic) = do
        tx <- newTyVar True False Nothing
        vtx <- mkVariadicTyArray isVariadic False tx
        e <- exprToken t
        ppe <- pp e
        x <- tcCoerces l isTop Nothing e vtx
        return (isConst,Right tx,isVariadic)

match :: BacktrackOpt -> Type -> Type -> TcCstr
match FullB x y = Unifies x y
match TryB x y = Unifies x y
match NoneB x y = Equals x y

tryTcError :: ProverK loc m => loc -> TcM m a -> TcM m (Either SecrecError a)
tryTcError l m = catchError (liftM Right $ newErrorM topm) (return . Left)
    where
    topm = tcNew (locpos l) "tryTcError" $ do
        x <- m
        solveTop l "tryTcError"
        return x


tryTcErrorMaybe :: ProverK loc m => loc -> TcM m a -> TcM m (Maybe a)
tryTcErrorMaybe l m = do
    mb <- tryTcError l m
    case mb of
        Right x -> return $ Just x
        Left _ -> return Nothing

cSec :: ComplexType -> Maybe SecType
cSec (CType s _ _) = Just s
cSec ct = Nothing

cSecM :: ProverK loc m => loc -> ComplexType -> TcM m SecType
cSecM l (CType s _ _) = return s
cSecM l (CVar v@(varIdRead -> True) isNotVoid) = resolveCVar l v isNotVoid >>= cSecM l
cSecM l Void = genTcError (locpos l) $ text "no security type for void"

isZeroIdxExpr :: ProverK loc m => loc -> Expr -> TcM m (Either SecrecError Bool)
isZeroIdxExpr l e = do
    ppe <- pp e
    i <- prove l ("isZeroIdxExpr " ++ show ppe) $ expr2SimpleIExpr $ fmap (Typed l) e
    mb <- tryTcError l $ isValid l (IBinOp IEq i $ ILit $ IUint64 0)
    case mb of
        Right () -> return $ Right True
        Left err -> if isHaltError err
            then return $ Left $ TypecheckerError (locpos l) $ GenTcError (text "failed to check if dimension" <+> ppe <+> text "== 0") (Just err)
            else do
                mb <- tryTcError l $ isValid l (IBinOp IGt i $ ILit $ IUint64 0)
                case mb of
                    Right () -> return $ Right False
                    Left err -> return $ Left $ TypecheckerError (locpos l) $ GenTcError (text "failed to check if dimension" <+> ppe <+> text "> 0") (Just err)
                        
snapCstrsM :: ProverK loc m => loc -> TcM m a -> TcM m (a,([TCstr],Set VarIdentifier))
snapCstrsM l m = do
    ((x,d),fs,_) <- withFrees l $ tcWith (locpos l) "snap" $ tcAddDeps (locpos l) "snap" m
    addHeadTDict l "snap" $ d { tCstrs = Graph.empty }
    let ks = map (kCstr . unLoc) $ Set.toList $ flattenIOCstrGraphSet $ tCstrs d
    return (x,(ks,Map.keysSet fs))
    




                        