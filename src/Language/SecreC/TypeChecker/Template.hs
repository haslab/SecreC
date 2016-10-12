{-# LANGUAGE TupleSections, ImpredicativeTypes, Rank2Types, ViewPatterns, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Monad
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Utils as Utils
import Language.SecreC.Pretty
import Language.SecreC.Position
import Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import Language.SecreC.Prover.Base

import Safe

import Data.List as List
import Data.Typeable
import Data.Either
import Data.Maybe
import Data.Unique
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set(..))
import Data.Map (Map(..))
import Data.Foldable
import Data.Graph.Inductive.Graph as Graph
import Data.Generics hiding (GT)

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Control.Monad.State as State

import Text.PrettyPrint as PP

instance (MonadIO m) => Vars GIdentifier (TcM m) [(Bool,Var,IsVariadic)] where
    traverseVars f = mapM f

instance (MonadIO m) => Vars GIdentifier (TcM m) [(IsConst,Either Expr Type,IsVariadic)] where
    traverseVars f = mapM f
    
--instance PP m VarIdentifier => PP m [(IsConst,Either Expr Type,IsVariadic)] where
--    pp xs = do
--        let f (z,x,y) = liftM (ppConst z) (ppVariadicArg pp (x,y))
--        liftM (sepBy comma) (mapM f xs)

instance PP m VarIdentifier => PP m [Either Expr Type] where
    pp xs = liftM (sepBy comma) (mapM pp xs)
    
instance (MonadIO m) => Vars GIdentifier (TcM m) [(Constrained Type,IsVariadic)] where
    traverseVars f = mapM f

instance PP m VarIdentifier => PP m [(Bool,Var,IsVariadic)] where
    pp xs = do
        let f (x,y,z) = do
            ppyz <- ppVariadicArg pp (y,z)
            return $ ppConst x ppyz
        liftM (sepBy comma) (mapM f xs)

instance PP m VarIdentifier => PP m [(Constrained Type,IsVariadic)] where
    pp = liftM (sepBy comma) . mapM (\(y,z) -> ppVariadicArg pp (y,z))

instance PP m VarIdentifier => PP m [(Expr,Var)] where
    pp xs = do
        let f (e,v) = do
            ppe <- ppExprTy e
            ppv <- ppVarTy v
            return $ ppe <+> text "~~>" <+> ppv
        liftM (sepBy comma) (mapM f xs)
    
instance PP m VarIdentifier => PP m [(Var,IsVariadic)] where
    pp = liftM (sepBy comma) . mapM (\(y,z) -> ppVariadicArg pp (y,z))

-- the most specific entries are preferred
sortEntries :: [EntryEnv] -> [EntryEnv]
sortEntries = sortBy sortDec
    where
    sortDec :: EntryEnv -> EntryEnv -> Ordering
    sortDec (EntryEnv _ (DecT d1)) (EntryEnv _ (DecT d2)) = compare (length $ decLineage d2) (length $ decLineage d1) 

decLineage :: DecType -> [ModuleTyVarId]
decLineage (DecType i j _ _ _ _ _) = i : maybeToList j

-- Procedure arguments are maybe provided with index expressions
-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: (ProverK loc m) => loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> TcM m [EntryEnv] -> TcM m DecType
matchTemplate l kid n targs pargs ret check = do
    entries <- liftM sortEntries check
    debugTc $ do
        ppentries <- mapM (pp . entryType) entries
        liftIO $ putStrLn $ "matches " ++ show (vcat $ ppentries)
    (instances,_) <- instantiateTemplateEntries Set.empty l kid n targs pargs ret entries
    let oks = rights instances
    let errs = lefts instances
    def <- ppTpltAppM l n targs pargs ret
    opts <- askOpts
    case oks of
        [] -> do
            defs <- forM errs $ \(e,err) -> do
                t' <- ppM l $ entryType e
                return (locpos $ entryLoc e,t',err)
            isAnn <- getAnn
            isLeak <- getLeak
            kind <- getKind
            tcError (locpos l) $ Halt $ NoMatchingTemplateOrProcedure (ppid isAnn <+> ppid isLeak <+> ppid kind <+> def) defs
        [inst] -> liftM fst $ resolveTemplateEntry False l kid n targs pargs ret inst
        -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
        otherwise -> if backtrack opts
            then do
                insts <- compMins (compareTemplateDecls def l (implicitCoercions opts) n) [] oks
                dec <- resolveTemplateEntries l kid n targs pargs ret insts
                debugTc $ do
                    n <- State.gets (length . tDict)
                    ppkid <- ppr kid
                    ppdec <- ppr dec
                    ppn <- ppr n
                    liftIO $ putStrLn $ "matchedTemplate " ++ ppkid ++ " " ++ ppdec ++ " " ++ ppn
                return dec
            else do
                (inst:insts) <- sortByM (\x y -> compareTemplateDecls def l False n x y >>= uncurry (appendOrdering l)) oks
                mapM_ discardMatchingEntry insts
                liftM fst $ resolveTemplateEntry False l kid n targs pargs ret inst

-- sort the templates, filtering out greater templates that do not rely on coercions
compMins :: Monad m => (a -> a -> m (Ordering,Ordering)) -> [a] -> [a] -> m [a]
compMins cmp [] (a:b:xs) = do
    (o,is) <- cmp a b
    case (o,is) of
        (EQ,EQ) -> compMins cmp [a,b] xs -- keep both
        (EQ,LT) -> compMins cmp [a,b] xs -- keep both
        (EQ,GT) -> compMins cmp [b,a] xs -- keep both
        (LT,EQ) -> compMins cmp [a] xs -- keep first
        (LT,LT) -> compMins cmp [a] xs -- keep first
        (GT,EQ) -> compMins cmp [b] xs -- keep both
        (GT,GT) -> compMins cmp [b] xs -- keep both
compMins cmp (min:mins) (x:xs) = do
    (o,is) <- cmp x min
    case (o,is) of
        (EQ,EQ) -> compMins cmp (x:min:mins) xs
        (EQ,LT) -> compMins cmp (x:min:mins) xs
        (EQ,GT) -> insertByM compMin x mins >>= \mins' -> compMins cmp (min:mins') xs
        (LT,EQ) -> compMins cmp [x] xs
        (LT,LT) -> compMins cmp [x] xs
        (GT,EQ) -> compMins cmp (min:mins) xs
        (GT,GT) -> compMins cmp (min:mins) xs
  where compMin x y = liftM (uncurry mappend) (cmp x y)
compMins cmp mins [] = return mins

type EntryInst = (EntryEnv,EntryEnv,[(Type,IsVariadic)],TDict,TDict,Frees,Frees,CstrCache)

discardMatchingEntry :: ProverK Position m => EntryInst -> TcM m ()
discardMatchingEntry (e,e',_,dict,_,frees,_,_) = forM_ (Map.keysSet frees) removeFree

mkInvocationDec :: ProverK loc m => loc -> DecType -> [(Type,IsVariadic)] -> TcM m DecType
mkInvocationDec l dec@(DecType j (Just (i)) targs hdict bdict specs d) targs' = return dec
mkInvocationDec l dec@(DecType i Nothing targs hdict bdict specs d) targs' = do
    j <- newModuleTyVarId
    ts' <- concatMapM (expandVariadicType l) targs'
    let specs' = map (,False) ts'
    return $ DecType j (Just (i)) [] hdict bdict specs' d

resolveTemplateEntries :: (ProverK loc m) => loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> [EntryInst] -> TcM m DecType
resolveTemplateEntries l kid n targs pargs ret [inst] = do
    liftM fst $ resolveTemplateEntry False l kid n targs pargs ret inst
resolveTemplateEntries l kid n targs pargs ret insts = do
    debugTc $ do
        ppkid <- ppr kid
        let ppes = show $ map (\(e,_,_,_,_,_,_,_) -> pprid $ decTypeTyVarId $ unDecT $ entryType e) insts
        liftIO $ putStrLn $ "resolveTemplateEntries " ++ ppkid ++ " " ++ ppes
    let choice refresh inst@(e,_,_,_,_,frees,_,_) = do
        ppkid <- pp kid
        pptyid <- pp (decTypeTyVarId $ unDecT $ entryType e)
        let match = (resolveTemplateEntry refresh l kid n targs pargs ret inst,text "resolveTemplateEntry" <+> ppkid <+> pptyid)
        let post (dec,heads) = return (heads,dec)
        return $ (match,(return,PP.empty),(post,PP.empty),Map.keysSet frees)
    choices' <- mapM (choice True) (init insts)
    choice' <- choice False (last insts)
    multipleSubstitutions l kid SolveAll (n,targs,pargs,ret) (choices'++[choice'])

resolveTemplateEntry :: (ProverK loc m) => Bool -> loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> EntryInst -> TcM m (DecType,Set LocIOCstr)
resolveTemplateEntry solveHead p kid n targs pargs ret (olde,e,targs',headDict,bodyDict,frees,delfrees,solved) = do
    debugTc $ do
        ppn <- ppr n
        pptargs <- ppr targs
        pppargs <- ppr pargs
        ppe <- ppr e
        pph <- ppr headDict
        ppb <- ppr bodyDict
        liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppn ++ " " ++ pptargs ++ " " ++ pppargs ++ " promoted " ++ ppe ++ "\nhead: " ++ pph ++ "\nbody: " ++ ppb
    -- add solved constraints
    addCstrCache p solved
    -- delete promoted constraints
    --buildCstrGraph p promoted promoted
    -- remove frees
    addFrees frees
    delFrees delfrees
    def <- ppTpltAppM p n targs pargs ret
    -- guarantee that the most specific template can be fully instantiated
    olddec <- typeToDecType p (entryType olde)
    dec <- typeToDecType p (entryType e)
    forM_ (Map.toList $ decTypeFrees dec) $ \(v,isVariadic) -> addFree v isVariadic
    --liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppr n ++ " " ++ ppr targs ++ " " ++ ppr pargs ++ " " ++ ppr dec
    -- prove the body (with a recursive declaration)
    let doWrap = isTemplateDecType olddec && not (decIsRec olddec)
    (decrec,rec) <- if doWrap
        then do
            decrec <- mkInvocationDec p dec targs'
            rec <- mkDecEnv p decrec
            return (decrec,rec)
        else return (dec,mempty)
    lineage <- getLineage
    let did = fromJustNote "resolveDecId" (decTypeId decrec)
    debugTc $ do
        ppdid <- ppr did
        pplineage <- mapM pp lineage
        liftIO $ putStrLn $ "resolveTplt "
            ++ show (isTemplateDecType olddec) ++ show (decIsRec olddec)
            ++ " " ++ ppdid ++ " : " ++ show (sepBy comma pplineage)
    addHeadTDictDirty p "resolveTemplateEntry" $ templateCstrs (did : lineage) rec def p headDict
    let headCstrs = Set.fromList $ map (snd) $ Graph.labNodes $ tCstrs headDict
    addHeadTDict p "resolveTemplateEntry" $ templateCstrs (did : lineage) rec def p $ bodyDict
    linkDependentCstrs p headDict bodyDict
    case n of
        TIden _ -> return ()
        otherwise -> do
            let tycl@(DecClass isAnn isInline rs ws) = tyDecClass $ DecT decrec
            exprC <- getExprC
            let isEmpty = either not Map.null
            case exprC of
                PureExpr -> unless (isEmpty rs && isEmpty ws) $ genTcError (locpos p) $ text "procedure not pure" <+> def
                ReadOnlyExpr -> unless (isEmpty ws) $ genTcError (locpos p) $ text "procedure not read-only" <+> def
                ReadWriteExpr -> return ()
            addDecClass tycl
    return (decrec,headCstrs)

templateCstrs :: Location loc => Lineage -> ModuleTcEnv -> Doc -> loc -> TDict -> TDict
templateCstrs lineage rec doc p d = d { tCstrs = Graph.nmap upd (tCstrs d), tRec = tRec d `mappend` rec }
    where
    upd (Loc l k) = Loc l $ k { kCstr = updCstrState (\st -> st { cstrLineage = lineage}) (kCstr k) }

variadicDecCtx :: DecCtx -> DecCtx
variadicDecCtx (DecCtx is d fs) = DecCtx is d $ variadicFrees fs

-- removes type arguments from a template declaration, as a step of instantiation
removeTemplate :: (ProverK loc m) => loc -> DecType -> TcM m (DecType,[(Constrained Var,IsVariadic)])
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(ProcType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) [] d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(FunType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) [] d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(LemmaType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) [] d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(AxiomType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) [] d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx [] d@(StructType {})) = do
    let specs' = map (mapFst (varNameToType . unConstrained)) targs
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs' d,targs)
removeTemplate l t@(DecType i isRec targs hctx bctx specs d@(StructType {})) = do
    return (DecType i isRec [] (variadicDecCtx hctx) (variadicDecCtx bctx) specs d,targs)
removeTemplate l (DVar v@(varIdRead -> True)) = resolveDVar l v >>= removeTemplate l

variadicFrees :: Frees -> Frees
variadicFrees = Map.filter (\b -> b)

ppTpltAppM :: (ProverK loc m) => loc -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> TcM m Doc
ppTpltAppM l pid args es ret = do
    ss <- getTSubsts l
    pid' <- substFromTSubsts "ppTplt" l ss False Map.empty pid
    args' <- mapM (mapM (mapFstM (substFromTSubsts "ppTplt" l ss False Map.empty))) args
    es' <- mapM (mapM (mapSnd3M (substFromTSubsts "ppTplt" l ss False Map.empty))) es
    ret' <- substFromTSubsts "ppTplt" l ss False Map.empty ret
    ppTpltApp pid' args' es' ret'

ppTpltApp :: ProverK Position m => TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> TcM m Doc
ppTpltApp (TIden n) args Nothing Nothing = do
    ppn <- pp n
    ppargs <- mapM (ppVariadicArg pp) $ concat $ args
    return $ text "struct" <+> ppn <> abrackets (sepBy comma ppargs)
ppTpltApp (PIden n) targs args (Just ret) = do
    ppret <- pp ret
    ppn <- pp n
    pptargs <- ppOpt targs pp
    ppargs <- ppOpt args pp
    return $ ppret <+> ppn <> abrackets pptargs <> parens ppargs
ppTpltApp (OIden n) targs args (Just ret) = do
    ppret <- pp ret
    ppn <- pp n
    pptargs <- ppOpt targs pp
    ppargs <- ppOpt args pp
    return $ ppret <+> ppn <> abrackets pptargs <> parens ppargs

compareTwice :: (ProverK loc m,PP (TcM m) x,VarsG (TcM m) x) => loc -> x -> x -> x -> x -> (x -> x -> TcM m (Comparison (TcM m))) -> (x -> x -> TcM m (Comparison (TcM m))) -> TcM m (Comparison (TcM m))
compareTwice l x x' y y' cmp1 cmp2 = do
    o <- cmp1 x y
    --debugTc $ do
    --    ppo <- ppr o
    --    liftIO $ putStrLn $ "comparing before " ++ ppo
    case compOrdering o of
        (ord,isLat) -> case ord of
            EQ -> return o
            otherwise -> do
                o' <- cmp2 x' y'
                --debugTc $ do
                --    ppo' <- ppr o'
                --    liftIO $ putStrLn $ "comparing after " ++ ppo'
                case compOrdering o' of
                    (EQ,_) -> return o
                    otherwise -> do
                        ppo <- ppr o
                        ppo' <- ppr $ compOrdering o'
                        constraintError (\x y mb -> Halt $ ComparisonException ("comparetwice " ++ ppo ++ "\n" ++ ppo') x y mb) l x' pp y' pp Nothing

--comparesListTwice :: (ProverK loc m) => loc -> Bool -> [Type] -> [Type] -> [Type] -> [Type] -> TcM m (Comparison (TcM m))
--comparesListTwice l isLattice a@[] a'@[] b@[] b'@[] = return $ Comparison a b EQ EQ
--comparesListTwice l isLattice a@(x:xs) a'@(x':xs') b@(y:ys) b'@(y':ys') = do
--    f <- compareTwice l x x' y y' (compares l isLattice)
--    g <- comparesListTwice l isLattice xs xs' ys ys'
--    appendComparison l f g
--comparesListTwice l isLattice xs xs' ys ys' = constraintError (ComparisonException "type") l xs pp ys pp Nothing

compareTypeArgs :: ProverK loc m => loc -> Bool -> [(Constrained Type,IsVariadic)] -> [(Constrained Type,IsVariadic)] -> TcM m (Comparison (TcM m))
compareTypeArgs l isLattice xs@[] ys@[] = return (Comparison xs ys EQ EQ)
compareTypeArgs l isLattice ((Constrained t1 c1,isVariadic1):xs) ((Constrained t2 c2,isVariadic2):ys) = do
    o1 <- compares l isLattice t1 t2
    unless (isVariadic1 == isVariadic2) $ constraintError (ComparisonException "type argument") l t1 pp t2 pp Nothing
    o2 <- compareTypeArgs l isLattice xs ys
    appendComparisons l [o1,o2]
compareTypeArgs l isLattice xs ys = constraintError (ComparisonException "type argument") l xs pp ys pp Nothing

compareProcedureArgs :: (ProverK loc m) => loc -> Bool -> [(Bool,Var,IsVariadic)] -> [(Bool,Var,IsVariadic)] -> TcM m (Comparison (TcM m))
compareProcedureArgs l isLattice xs@[] ys@[] = return (Comparison xs ys EQ EQ)
compareProcedureArgs l isLattice ((_,v1@(VarName t1 n1),isVariadic1):xs) ((_,v2@(VarName t2 n2),isVariadic2):ys) = do
--    liftIO $ putStrLn $ "comparePArgExp " ++ ppr v1 ++ " " ++ ppr v2 ++ " "
    o0 <- comparesExpr l True (varExpr v1) (varExpr v2)
--    liftIO $ putStr $ show (compOrdering o0)
    --ss <- getTSubsts l
    o1 <- compares l isLattice t1 t2
    --liftIO $ putStrLn $ "comparePArg " ++ ppr t1 ++ " " ++ ppr t2 ++ " " ++ ppr ss ++"\n= " ++ ppr o1
--    liftIO $ putStr $ show (compOrdering o1)
    unless (isVariadic1 == isVariadic2) $ constraintError (ComparisonException "procedure argument") l t1 pp t2 pp Nothing
    o2 <- compareProcedureArgs l isLattice xs ys
    appendComparisons l [o0,o1,o2]
compareProcedureArgs l isLattice xs ys = constraintError (ComparisonException "procedure argument") l xs pp ys pp Nothing

-- | Tells if one declaration is strictly more specific than another, and if not it fails.
-- Since we are unifying base types during instantiation, it may happen that the most specific match is chosen over another more generic best match. This problem does not arise though if we only resolve templates on full instantiation. If we ever change this, we should use instead a three-way comparison that also tries to minimize the number of instantiated type variables in the context.
-- An example is if we tried to match the template over a type variable T:
-- y = f ((T) x)
-- bool f (int x) { ... }     (1)
-- bool f (T x) { ... }       (2)
-- bool f (T [[N]] x) { ... } (3)
-- We would be choosing (1), even though the best match is in principle (2), that does not instantiate T.
-- doesn't take into consideration index conditions
-- compare original declarations, not instantiated ones
compareTemplateDecls :: (ProverK loc m) => Doc -> loc -> Bool -> TIdentifier -> EntryInst -> EntryInst -> TcM m (Ordering,Ordering)
compareTemplateDecls def l isLattice n (e1,e1',_,d1,_,_,_,_) (e2,e2',_,d2,_,_,_,_) = liftM fst $ tcProveTop l "compare" $ tcBlock $ do
    ord <- compareTwice l e1 e1' e2 e2' (compareTemplateEntries True def l isLattice n) (compareTemplateEntries False def l isLattice n)
    debugTc $ do
        ppo <- pp ord
        liftIO $ putStrLn $ "finished comparing decls " ++ show ppo
    return $ compOrdering ord
    
compareTemplateEntries :: (ProverK loc m) => Bool -> Doc -> loc -> Bool -> TIdentifier -> EntryEnv -> EntryEnv -> TcM m (Comparison (TcM m))
compareTemplateEntries notEq def l isLattice n e1 e2 = liftM fst $ tcProveTop l "compare" $ tcBlock $ do
    debugTc $ do
        pp1 <- ppr e1
        pp2 <- ppr e2
        liftIO $ putStrLn $ "compareTemplateDecls " ++ pp1 ++ "\n" ++ pp2
    State.modify $ \env -> env { localDeps = Set.empty, globalDeps = Set.empty }
    (targs1,pargs1,ret1) <- templateArgs (entryLoc e1) n (entryType e1)
    (targs2,pargs2,ret2) <- templateArgs (entryLoc e2) n (entryType e2)
    unless (isJust ret1 == isJust ret2) $ do
        ppe1 <- ppr e1
        ppe2 <- ppr e2
        error $ "declarations should have the same return type " ++ ppe1 ++ "\n" ++ ppe2
    let f e = do
        ppe <- pp (entryType e) 
        return $ (locpos $ entryLoc e,ppe)
    defs <- mapM f [(e1),(e2)]
    let err = TypecheckerError (locpos l) . Halt . ConflictingTemplateInstances def defs
    ord <- addErrorM l err $ do
        ord2 <- if (isJust ret1)
            -- for procedures, compare the procedure arguments
            then compareProcedureArgs l isLattice (concat pargs1) (concat pargs2)
            -- for structs, compare the specialization types
            else compareTypeArgs l isLattice (concat targs1) (concat targs2)
        ord3 <- comparesList l isLattice (maybeToList ret1) (maybeToList ret2)
        ord4 <- if notEq then comparesDecIds (entryType e1) (entryType e2) else return $ Comparison (entryType e1) (entryType e2) EQ EQ
        appendComparisons l [ord2,ord3,ord4]
    let (o,isLat) = compOrdering ord
    when (notEq && mappend o isLat == EQ) $ tcError (locpos l) $ Halt $ DuplicateTemplateInstances def defs
    return ord

-- favor specializations over the base template
comparesDecIds d1@(DecT (DecType j1 (Just (i1)) _ _ _ _ _)) d2@(DecT (DecType j2 Nothing _ _ _ _ _)) | i1 == j2 = return $ Comparison d1 d2 LT EQ
comparesDecIds d1@(DecT (DecType j1 Nothing _ _ _ _ _)) d2@(DecT (DecType j2 (Just (i2)) _ _ _ _ _)) | j1 == i2 = return $ Comparison d1 d2 GT EQ
comparesDecIds d1@(DecT (DecType j1 (Just i1) _ _ _ _ _)) d2@(DecT (DecType j2 (Just (i2)) _ _ _ _ _)) | i1 == i2 = return $ Comparison d1 d2 LT EQ -- choose one of them since they are instantiations of the same declaration
comparesDecIds d1 d2 = return $ Comparison d1 d2 EQ EQ -- do nothing
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (ProverK loc m) => Set ModuleTyVarId -> loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> [EntryEnv] -> TcM m ([Either (EntryEnv,SecrecError) EntryInst],Set ModuleTyVarId)
instantiateTemplateEntries valids l kid n targs pargs ret [] = return ([],Set.empty)
instantiateTemplateEntries valids l kid n targs pargs ret (e:es) = do
    let d = unDecT (entryType e)
    let did = fromJustNote "instantiate" $ decTypeTyVarId d
    -- skip declarations whose instantiations have already matched
    if Set.member did valids
        then instantiateTemplateEntries valids l kid n targs pargs ret es
        else do
            r <- instantiateTemplateEntry l kid n targs pargs ret e
            let valids' = case r of
                            Left _ -> valids
                            Right _ -> (Set.fromList $ decLineage d) `Set.union` valids
            (rs,valids'') <- instantiateTemplateEntries valids' l kid n targs pargs ret es
            return (r:rs,valids'')

unifyTemplateTypeArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [(Constrained Type,IsVariadic)] -> TcM m ()
unifyTemplateTypeArgs l lhs rhs = do
--    liftIO $ putStrLn $ "unifyTpltTyArg " ++ ppr lhs ++ " " ++ ppr (map (\(x,y) -> (unConstrainedx,y)) rhs)
    (cs,ks) <- tcWithCstrs l "unity tplt type args" $ do
        -- expand the passed type arguments
        ts <- concatMapM (expandVariadicType l) lhs
        -- separate procedure argument types from their conditions
        let (tts,catMaybes -> tcs) = unzip $ map (\(Constrained t c,b) -> ((t,b),c)) rhs
        -- match each procedure argument type
        pptts <- pp tts
        ppts <- pp ts
        addErrorM l
            (TypecheckerError (locpos l) . (UnificationException "template type arguments") (pptts) (ppts) . Just)
            (matchVariadicTypeArgs l tts ts)
        return tcs
    -- check the procedure argument conditions
    forM_ cs $ \c -> withDependencies ks $ tcCstrM_ l $ IsValid c      

matchVariadicTypeArgs :: (ProverK loc m) => loc -> [(Type,IsVariadic)] -> [Type] -> TcM m ()
matchVariadicTypeArgs l [] [] = return ()
matchVariadicTypeArgs l xs@[] ys = do
    ppxs <- pp xs
    ppys <- pp ys
    genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> ppxs <+> ppys
matchVariadicTypeArgs l (x:xs) ys = do
    ys' <- matchVariadicTypeArg l x ys
    matchVariadicTypeArgs l xs ys'

-- matches a procedure argument type with a list of types, and produces a remainder of unmatched types
matchVariadicTypeArg :: (ProverK loc m) => loc -> (Type,IsVariadic) -> [Type] -> TcM m [Type]
matchVariadicTypeArg l x@(t,False) ys@[] = do
    ppx <- pp x
    ppys <- pp ys
    genTcError (locpos l) $ text "Template type argument variadic mismatch" <+> ppx <+> ppys
matchVariadicTypeArg l (t,False) (y:ys) = do
    tcCstrM_ l $ Unifies t y
    return ys
matchVariadicTypeArg l (VArrayT (VAVal ts _),True) xs = do
    let (xs1,xs2) = splitAt (length ts) xs
    unifiesList l ts xs1
    return xs2
matchVariadicTypeArg l (t,True) xs = do
    let tt = tyOf t
    sz <- typeSize l tt
    b <- typeBase l tt
    (xs1,xs2) <- spanM (isTyOf l b) xs
    -- match the array content
    tcCstrM_ l $ Unifies t (VArrayT $ VAVal xs1 b)
    -- match the array size
    unifiesExprTy l True sz (indexExpr $ toEnum $ length xs1)
    return xs2      

matchVariadicPArgs :: (ProverK loc m) => loc -> [(Bool,Expr,IsVariadic)] -> [Either Expr Type] -> TcM m ()
matchVariadicPArgs l [] [] = return ()
matchVariadicPArgs l xs@[] ys = do
    ppxs <- pp (map (\(x,y,z) -> (y,z)) xs)
    ppys <- pp ys
    genTcError (locpos l) $ text "Procedure argument variadic mismatch" <+> ppxs <+> ppys
matchVariadicPArgs l (x:xs) ys = do
    ys' <- matchVariadicPArg l x ys
    matchVariadicPArgs l xs ys'

matchVariadicPArg :: (ProverK loc m) => loc -> (Bool,Expr,IsVariadic) -> [Either Expr Type] -> TcM m [Either Expr Type]
matchVariadicPArg l (isConst,v,False) exs@[] = do
    ppv <- pp v
    ppexs <- pp exs
    genTcError (locpos l) $ text "Procedure argument variadic mismatch" <+> ppv <+> ppexs
matchVariadicPArg l (isConst,v,False) (e:exs) = do
    matchPArg l isConst v e
    return exs
matchVariadicPArg l (isConst,v,True) exs = do
    let t = loc v
    case t of
        VArrayT (VAVal ts b) -> do
            let (exs1,exs2) = splitAt (length ts) exs
            vs <- expandVariadicExpr l isConst (v,True)
            matchVariadicPArgs l (map (\v -> (isConst,v,False)) vs) exs1
            return exs2
        otherwise -> do
            sz <- typeSize l t
            b <- typeBase l t
            (unzip -> (vs,exs1),exs2) <- flip spanMaybeM exs $ \ex -> tryCstrMaybe l $ do
                v <- newTypedVar "vel" b (not isConst) Nothing
                matchPArg l isConst (varExpr v) ex >> return (v,ex)
            -- match the array size
            unifiesExprTy l True sz (indexExpr $ toEnum $ length exs1)
            -- match the array content
            --if isConst
            -- variadic arrays are themselves always constant
            unifiesExprTy l True v (ArrayConstructorPExpr t $ map varExpr vs)
                --else tcCstrM_ l $ Unifies (loc v) t
            return exs2

matchPArg :: (ProverK loc m) => loc -> Bool -> Expr -> Either Expr Type -> TcM m ()
matchPArg l isConst v2 (Right t) = do
    tcCstrM_ l $ Unifies (loc v2) t
matchPArg l isConst v2 (Left e) = do
    --liftIO $ putStrLn $ show $ text "coercePArg" <+> pp isConst <+> ppExprTy v2 <+> ppExprTy e <+> ppExprTy x2
    if isConst
        then unifiesExprTy l True v2 e
        else tcCstrM_ l $ Unifies (loc v2) (loc e)

expandPArgExpr :: (ProverK loc m) => loc -> (IsConst,Either Expr Type,IsVariadic) -> TcM m [Either Expr Type]
expandPArgExpr l (_,Left e,False) = return [Left e]
expandPArgExpr l (_,Left e,True) = do
    es <- expandVariadicExpr l False (e,True)
    return $ map Left es
expandPArgExpr l (_,Right t,True) = do
    ts <- expandVariadicType l (t,True)
    return $ map (Right) ts

matchProcedureArgs :: (ProverK loc m) => loc -> [(IsConst,Either Expr Type,IsVariadic)] -> [(Bool,Var,IsVariadic)] -> TcM m ()
matchProcedureArgs l lhs rhs = do
    (_,ks) <- tcWithCstrs l "coerce proc args" $ do
        -- expand passed expressions
        exs <- concatMapM (expandPArgExpr l) lhs
        -- separate procedure arguments from their conditions
        let (vs) = map (\(isConst,v,b) -> ((isConst,varExpr v,b))) rhs
        -- match each procedure argument
        ppexs <- pp exs
        ppvs <- pp $ map (\(x,y,z) -> (y,z)) vs
        addErrorM l
            (TypecheckerError (locpos l) . (CoercionException "procedure arguments") (ppexs) (ppvs) . Just)
            (matchVariadicPArgs l vs exs)
        return ()
    return ()

mapErr :: (Either (EntryEnv,SecrecError) (EntryEnv,EntryEnv,[(Type,IsVariadic)],TDict,TDict,CstrCache),Frees,Frees) -> Either (EntryEnv,SecrecError) EntryInst
mapErr (Left x,_,_) = Left x
mapErr (Right (x1,x2,x3,x4,x5,x6),y,z) = Right (x1,x2,x3,x4,x5,y,z,x6)

checkRecursiveDec :: ProverK loc m => loc -> DecType -> TcM m Bool
checkRecursiveDec l d@(DecType _ isRec _ _ _ _ _) = do
    case isRec of
        Nothing -> return False
        Just i -> do
            lin <- getLineage
            let did = fromJustNote "checkRecursiveDec" $ decTypeId d
            return $ List.elem did lin

instantiateTemplateEntry :: (ProverK loc m) => loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(IsConst,Either Expr Type,IsVariadic)] -> Maybe Type -> EntryEnv -> TcM m (Either (EntryEnv,SecrecError) EntryInst)
instantiateTemplateEntry p kid n targs pargs ret e@(EntryEnv l t@(DecT d)) = limitExprC ReadOnlyExpr $ newErrorM $ liftM mapErr $ withFrees p $ do
            --doc <- liftM ppTSubsts getTSubsts
            --liftIO $ putStrLn $ "inst " ++ show doc
            isRec <- checkRecursiveDec l d
            debugTc $ do
                ppp <- ppr l
                ppl <- ppr l
                ppn <- ppr n
                pptargs <- ppr (fmap (map fst) targs)
                ppargs <- mapM pp pargs
                ppret <- ppr ret
                ppte <- ppr (entryType e)
                liftIO $ putStrLn $ "instantiating " ++ ppp ++ " " ++ ppl ++ " " ++ ppn ++ " " ++ pptargs ++ " " ++ show ppargs ++ " " ++ ppret ++ " " ++ show isRec ++ "\n" ++ ppte
            -- can't instantiate recursive variables
            let chg v = if isRec then v { varIdWrite = False } else v
            (tplt_targs,tplt_pargs,tplt_ret) <- templateArgs l n t >>= chgVarId chg
            exprC <- getExprC
            (e',hdict,bdict,bgr) <- templateTDict exprC e
            let addDicts = do
                addHeadTDict l "instantiateTemplateEntry" hdict
                addHeadTDict l "instantiateTemplateEntry" bdict
            let matchName = unifiesTIdentifier l (templateIdentifier $ entryType e') n
            let proveHead = withoutEntry e $ do
                -- we remove the current entry while typechecking the head constraints
                (_,ks) <- tcWithCstrs l "instantiate" $ do   
                    tcAddDeps l "tplt type args" $ do
                        ppttargs <- liftM (sepBy comma) $ mapM (pp . fst) $ concat tplt_targs
                        --debugTc $ liftIO $ putStrLn $ "tplttargs: " ++ show ppttargs
                        -- unify the explicit invocation template arguments unify with the base template
                        when (isJust targs) $ tcAddDeps l "targs" $ unifyTemplateTypeArgs l (concat targs) (concat tplt_targs)
                        -- unify the procedure return type
                        unifiesList l (maybeToList tplt_ret) (maybeToList ret)
                        -- coerce procedure arguments into the base procedure arguments
                        matchProcedureArgs l (concat pargs) (concat tplt_pargs)
                -- if there are no explicit template type arguments, we need to make sure to check the type invariants
                when (isNothing targs) $ do
                    forM_ (maybe [] (catMaybes . map (\(Constrained x c,isVariadic) -> c)) tplt_targs) $ \c -> do
                        withDependencies ks $ tcCstrM_ l $ IsValid c
                return ()
            -- try to make progress on general constraints that may be bound to bindings of this instance
            let promote = do
                vs <- usedVs (n,targs,pargs,ret)
                tops <- topCstrs l
                let tops' = mapSet (ioCstrId . unLoc) tops
                rels <- relatedCstrs l (Set.toList tops') vs (filterCstrSetScope SolveLocal)
                let rels' = mapSet (ioCstrId . unLoc) rels
                buildCstrGraph l rels'
                debugTc $ do
                    ppl <- ppr l
                    ppvs <- ppr vs
                    pprels' <- ppr rels'
                    liftIO $ putStrLn $ "tpltVars " ++ ppl ++ " " ++ ppvs
                    liftIO $ putStrLn $ "relVars " ++ ppl ++ " " ++ pprels'
                    dicts <- State.gets tDict
                    ss <- ppConstraints (tCstrs $ head dicts)
                    liftIO $ putStrLn $ (concat $ replicate (length dicts) ">") ++ "tpltCstrs " ++ ppl ++ " [" ++ show ss ++ "\n]"
                    forM_ (tail dicts) $ \d -> do
                        ssd <- ppConstraints (tCstrs d)
                        liftIO $ putStrLn $ "\n[" ++ show ssd ++ "\n]"
                    --doc <- liftM ppTSubsts $ getTSubsts l
                    --liftIO $ putStrLn $ show doc
                return rels'
            mode <- defaultSolveMode
            ok <- orError $ tcWith (locpos p) "instantiate" $ do
                st <- getCstrState
                ppn <- ppr n
                ppp <- ppr l
                ppl <- ppr l
                addDicts >> matchName >> proveHead
                solveWith p ("instantiate with names " ++ ppn ++ " " ++ ppp ++ " " ++ ppl ++ " " ++ show mode) mode
                ((promoted,_),cache) <- withCstrState (locpos p) st $ onFrees p $ onCache $ tcProveWith l "promote" (mode { solveFail = FirstFail False }) $ promote
                return (cache)
            --ks <- ppConstraints =<< liftM (maybe Graph.empty tCstrs . headMay . tDict) State.get
            --liftIO $ putStrLn $ "instantiate with names " ++ ppr n ++ " " ++ show ks
            case ok of
                Left err -> do
                    debugTc $ do
                        ppn <- ppr n
                        pperr <- ppr err
                        liftIO $ putStrLn $ "failed to instantiate " ++ pprid kid ++ " " ++ ppn ++" "++ show (decTypeTyVarId $ unDecT $ entryType e) ++ "\n" ++ pperr
                    return $ Left (e,err)
                Right ((cache),TDict hgr _ subst recs) -> do
                        --removeIOCstrGraphFrees hgr
                        -- we don't need to rename recursive declarations, since no variables have been bound
                        (e',(subst',bgr',hgr',recs')) <- localTemplateWith l e' (subst,bgr,toPureCstrs hgr,recs)
                        bgr'' <- substFromTSubsts "instantiate tplt" l subst' False Map.empty bgr'
                        hgr'' <- substFromTSubsts "instantiate tplt" l subst' False Map.empty hgr'
                        recs'' <- substFromTSubsts "instantiate tplt" l subst' False Map.empty recs'
                        bgr1 <- fromPureCstrs bgr''
                        hgr1 <- fromPureCstrs hgr''
                        let headDict = (TDict hgr1 Set.empty subst' recs'')
                        let bodyDict = (TDict bgr1 Set.empty emptyTSubsts mempty)
                        --let headPureDict = toPureTDict headDict
                        --let bodyPureDict = toPureTDict bodyDict
                        debugTc $ do
                            pph <- ppConstraints $ tCstrs headDict
                            ppb <- ppConstraints $ tCstrs bodyDict
                            ppn <- ppr n
                            liftIO $ putStrLn $ "remainder " ++ pprid kid ++ " " ++ ppn ++" " ++ show (decTypeTyVarId $ unDecT $ entryType e) ++ " " ++ show pph ++"\n"++ show ppb
                        dec1 <- typeToDecType l (entryType e')
                        (dec2,targs') <- removeTemplate l dec1 >>= substFromTSubsts "instantiate tplt" l subst' False Map.empty
                        --let dec3 = addDecDicts dec2 headPureDict bodyPureDict
                        --debugTc $ liftIO $ putStrLn $ "withTplt: " ++ ppr l ++ "\n" ++ ppr subst ++ "\n+++\n"++ppr subst' ++ "\n" ++ ppr dec2
                        return $ Right (e,e' { entryType = DecT dec2 },map (mapFst (varNameToType . unConstrained)) targs',headDict,bodyDict,cache)

-- merge two dictionaries with the second depending on the first
linkDependentCstrs :: (ProverK loc m) => loc -> TDict -> TDict -> TcM m ()
linkDependentCstrs l from to = do
    let froms = map fst $ endsGr $ tCstrs from
    let tos = map fst $ rootsGr $ tCstrs to
    let deps = [ (f,t) | f <- froms, t <- tos ]
    let upd d (f,t) = d { tCstrs = insEdge (f,t,()) (tCstrs d) } 
    updateHeadTDict l "dependentCstrs" $ \d -> return ((),foldl' upd d deps)

templateIdentifier :: Type -> TIdentifier
templateIdentifier (DecT t) = templateIdentifier' t
    where
    templateIdentifier' :: DecType -> TIdentifier
    templateIdentifier' (DecType _ _ _ _ _ _ t) = templateIdentifier'' t
        where
        templateIdentifier'' (ProcType _ n _ _ _ _ _) = n
        templateIdentifier'' (FunType isLeak _ n _ _ _ _ _) = n
        templateIdentifier'' (AxiomType isLeak _ _ _ _) = error "no identifier for axiom"
        templateIdentifier'' (LemmaType isLeak _ n _ _ _ _) = n
        templateIdentifier'' (StructType _ (TIden n) _ _) = TIden n
   
-- has type or procedure constrained arguments     
--hasCondsDecType :: (MonadIO m) => DecType -> TcM m Bool
--hasCondsDecType (DecType _ _ targs _ _ _ _ _ d) = do
--    b <- hasCondsDecType d
--    return $ b || (any hasConstrained $ map fst targs)
--hasCondsDecType (ProcType _ _ pargs _ _ _ _) = return $ any hasConstrained $ map snd3 pargs
--hasCondsDecType _ = return False
 
-- | Extracts a head signature from a template type declaration (template arguments,procedure arguments, procedure return type)
templateArgs :: (MonadIO m,Location loc) => loc -> TIdentifier -> Type -> TcM m (Maybe [(Constrained Type,IsVariadic)],Maybe [(Bool,Var,IsVariadic)],Maybe Type)
templateArgs l (TIden name) t = case t of
    DecT d@(DecType _ isRec args hcstrs cstrs specs body) -> do 
        return (Just $ decTypeArgs d,Nothing,Nothing)
templateArgs l name t = case t of
    DecT d@(DecType _ isRec args hcstrs cstrs specs (ProcType _ n vars ret ann stmts _)) -> do -- include the return type
        return (Just $ decTypeArgs d,Just vars,Just ret)
    DecT d@(DecType _ isRec args hcstrs cstrs specs (FunType isLeak _ n vars ret ann stmts _)) -> do -- include the return type
        return (Just $ decTypeArgs d,Just vars,Just ret)
    DecT d@(DecType _ isRec args hcstrs cstrs specs (LemmaType isLeak _ n vars ann stmts _)) -> do
        return (Just $ decTypeArgs d,Just vars,Just $ ComplexT Void)
    DecT d@(DecType _ isRec args hcstrs cstrs specs (AxiomType isLeak _ vars ann _)) -> do
        return (Just $ decTypeArgs d,Just vars,Nothing)
    otherwise -> genTcError (locpos l) $ text "Invalid type for procedure template"

tpltTyVars :: Maybe [(Constrained Type,IsVariadic)] -> Set GIdentifier
tpltTyVars Nothing = Set.empty
tpltTyVars (Just xs) = Set.fromList $ map (varNameId . fromJust . typeToVarName . unConstrained . fst) xs

--addDecDicts :: DecType -> PureTDict -> PureTDict -> DecType
--addDecDicts (DecType i isRec vars hd bd specs ss) hd' bd' = DecType i isRec vars hd' bd' specs ss

templateTDict :: (ProverK Position m) => ExprClass -> EntryEnv -> TcM m (EntryEnv,TDict,TDict,TCstrGraph)
templateTDict exprC e = case entryType e of
    DecT (DecType i isRec vars (DecCtx his hd hfrees) (DecCtx bis d bfrees) specs ss) -> do
        hd' <- fromPureTDict $ hd { pureCstrs = purify $ pureCstrs hd }
        let d' = TDict Graph.empty Set.empty (pureSubsts d) (pureRec d)
        let e' = e { entryType = DecT (DecType i isRec vars (DecCtx his emptyPureTDict hfrees) (DecCtx bis emptyPureTDict bfrees) specs ss) }
        return (e',hd',d',purify $ pureCstrs d)
    otherwise -> return (e,emptyTDict,emptyTDict,Graph.empty)
  where
    purify :: TCstrGraph -> TCstrGraph
    purify = Graph.nmap (fmap add)
    add = updCstrState (\st -> st { cstrExprC = min exprC (cstrExprC st) })

condVarType (Constrained (VarName t n) c) = constrainedType t c
condVar (Constrained (VarName t n) c) = VarName (constrainedType t c) n
condT (Constrained t c) = constrainedType t c

--refreshEntryPVars :: ProverK loc m => loc -> EntryEnv -> Maybe [GIdentifier] -> TcM m EntryEnv
--refreshEntryPVars l e Nothing = return e
--refreshEntryPVars l e@(EntryEnv p t) (Just vars') = case t of
--    DecT (DecType i (Just (k,Just vars)) ts hd hfrees bd bfrees specs b) -> do
--        debugTc $ do
--            ppvars' <- ppr vars'
--            ppvars <- ppr vars
--            liftIO $ putStrLn $ "refreshEntryPVars: dropping " ++ ppvars ++ " for " ++ ppvars'
--        forM_ vars $ \(VIden v) -> removeFree v
--        let ss = emptySubstsProxy
--        let ssBounds = Map.fromList $ zip vars vars'
--        hd' <- substProxy "refreshEntryPVars" ss False ssBounds $ deleteSubsts (map unVIden vars) hd
--        hfrees' <- liftM (Map.mapKeys unVIden) $ substProxy "refreshEntryPVars" emptySubstsProxy False ssBounds $ Map.mapKeys VIden hfrees
--        return $ EntryEnv p $ DecT $ DecType i (Just (k,Just vars')) ts hd' hfrees' bd bfrees specs b
--    otherwise -> return e

deleteSubsts :: [VarIdentifier] -> PureTDict -> PureTDict
deleteSubsts vs d = d { pureSubsts = TSubsts $ deletes vs $ unTSubsts $ pureSubsts d }
    where
    deletes [] xs = xs
    deletes (v:vs) xs = Map.delete v (deletes vs xs)

-- | renames the variables in a template to local names
localTemplate :: (ProverK loc m) => loc -> EntryEnv -> TcM m EntryEnv
localTemplate l e = liftM fst $ localTemplateWith l e ()

localTemplateDec :: (ProverK loc m) => loc -> DecType -> TcM m DecType
localTemplateDec l dec = do
    t <- liftM (entryType . fst) $ localTemplateWith l (EntryEnv (locpos l) $ DecT dec) ()
    typeToDecType l t

localTemplateWith :: (Vars GIdentifier (TcM m) a,ProverK loc m) => loc -> EntryEnv -> a -> TcM m (EntryEnv,a)
localTemplateWith l e a = case entryType e of
    DecT t -> do
        debugTc $ do
            ppl <- ppr l
            ppt <- ppr t
            liftIO $ putStrLn $ "localTemplate: " ++ ppl ++ "\n" ++ ppt
        (t',ss,ssBounds) <- localTemplateType emptySubstsProxy Map.empty (entryLoc e) t
        debugTc $ do
            ppl <- ppr l
            ppbounds <- ppr ssBounds
            liftIO $ putStrLn $ "localSS: " ++ ppl ++ "\n" ++ ppbounds
        debugTc $ do
            ppl <- ppr l
            ppt' <- ppr t'
            liftIO $ putStrLn $ "localTemplate': " ++ ppl ++ "\n" ++ ppt'
        a' <- substProxy "localTplt" ss False ssBounds a
        debugTc $ do
            ppl <- ppr l
            ppa' <- ppr a'
            liftIO $ putStrLn $ "localTemplateReturn: " ++ ppl ++ ppa'
        return (EntryEnv (entryLoc e) $ DecT t',a')

localTemplateType :: (ProverK loc m) => SubstsProxy GIdentifier (TcM m) -> Map GIdentifier GIdentifier -> loc -> DecType -> TcM m (DecType,SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier)
localTemplateType (ss::SubstsProxy GIdentifier (TcM m)) ssBounds (l::loc) et = case et of
    DecType tpltid isrec args hctx bctx (unzip -> (specials,isVariadics2)) body -> do
        (hctx',ss1,ssBounds1) <- localDecCtx ss ssBounds l hctx
        (args',ss2,ssBounds2) <- uniqueTyVars l ss1 ssBounds1 args
        specials' <- substProxy "localTplt" ss2 False ssBounds2 specials
        (bctx',ss3,ssBounds3) <- localDecCtx ss2 ssBounds2 l bctx
        (body',ss4,ssBounds4) <- localTemplateInnerType ss3 ssBounds3 l body
        return (DecType tpltid isrec args' hctx' bctx' (zip specials' isVariadics2) body',ss4,ssBounds4)

localDecCtx :: ProverK loc m => SubstsProxy GIdentifier (TcM m) -> Map GIdentifier GIdentifier -> loc -> DecCtx -> TcM m (DecCtx,SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier)
localDecCtx (ss::SubstsProxy GIdentifier (TcM m)) ssBounds l (DecCtx is dict frees) = do
    (frees',freelst) <- Utils.mapAndUnzipM freeVar $ Map.toList $ Map.mapKeys VIden frees
    let ss' :: SubstsProxy GIdentifier (TcM m)
        ss' = substsProxyFromList freelst `appendSubstsProxy` ss
    let ssBounds' = ssBounds `Map.union` Map.fromList freelst
    dict' <- substProxy "localTplt" ss' False ssBounds' dict
    return (DecCtx is dict' (Map.mapKeys unVIden $ Map.fromList $ frees'),ss',ssBounds')

localTemplateInnerType :: (ProverK loc m) => SubstsProxy GIdentifier (TcM m) -> Map GIdentifier GIdentifier -> loc -> InnerDecType -> TcM m (InnerDecType,SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier)
localTemplateInnerType (ss0::SubstsProxy GIdentifier (TcM m)) ssBounds (l::loc) et = case et of
    ProcType p pid args ret ann stmts c -> do
        (args',ss,ssBounds1) <- uniqueProcVars l ss0 ssBounds args
        pid' <- substProxy "localTplt" ss False ssBounds1 pid
        ret' <- substProxy "localTplt" ss False ssBounds1 ret
        ann' <- substProxy "localTplt" ss False ssBounds1 ann
        stmts' <- substProxy "localTplt" ss False ssBounds1 stmts
        c' <- substProxy "localTplt" ss False ssBounds1 c
        return (ProcType p pid' args' ret' ann' stmts' c',ss,ssBounds1)
    FunType isLeak p pid args ret ann stmts c -> do
        (args',ss,ssBounds1) <- uniqueProcVars l ss0 ssBounds args
        pid' <- substProxy "localTplt" ss False ssBounds1 pid
        ret' <- substProxy "localTplt" ss False ssBounds1 ret
        ann' <- substProxy "localTplt" ss False ssBounds1 ann
        stmts' <- substProxy "localTplt" ss False ssBounds1 stmts
        c' <- substProxy "localTplt" ss False ssBounds1 c
        return (FunType isLeak p pid' args' ret' ann' stmts' c',ss,ssBounds1)
    AxiomType isLeak p args ann c -> do
        (args',ss,ssBounds1) <- uniqueProcVars l ss0 ssBounds args
        ann' <- substProxy "localTplt" ss False ssBounds1 ann
        c' <- substProxy "localTplt" ss False ssBounds1 c
        return (AxiomType isLeak p args' ann' c',ss,ssBounds1)
    LemmaType isLeak p pid args ann stmts c -> do
        (args',ss,ssBounds1) <- uniqueProcVars l ss0 ssBounds args
        pid' <- substProxy "localTplt" ss False ssBounds1 pid
        ann' <- substProxy "localTplt" ss False ssBounds1 ann
        stmts' <- substProxy "localTplt" ss False ssBounds1 stmts
        c' <- substProxy "localTplt" ss False ssBounds1 c
        return (LemmaType isLeak p pid' args' ann' stmts' c',ss,ssBounds1)
    StructType p sid atts c -> do
        sid' <- substProxy "localTplt" ss0 False ssBounds sid
        atts' <- substProxy "localTplt" ss0 False ssBounds atts
        c' <- substProxy "localTplt" ss0 False ssBounds c
        return (StructType p sid' atts' c',ss0,ssBounds)
       
freeVar :: ProverK Position m => (GIdentifier,IsVariadic) -> TcM m ((GIdentifier,IsVariadic),(GIdentifier,GIdentifier))
freeVar (VIden v,isVariadic) = do
    ModuleTyVarId mn j <- newModuleTyVarId
    let v' = v { varIdUniq = Just j, varIdModule = Just mn }
    --addFree v'
    return ((VIden v',isVariadic),(VIden v,VIden v'))
    
uniqueTyVar :: ProverK loc m => loc -> SubstsProxy GIdentifier (TcM m) -> Map GIdentifier GIdentifier -> (Constrained Var,IsVariadic) -> TcM m ((Constrained Var,IsVariadic),SubstsProxy GIdentifier (TcM m), Map GIdentifier GIdentifier)
uniqueTyVar (l::loc) (ss::SubstsProxy GIdentifier (TcM m)) ssBounds (Constrained i@(VarName t (VIden v@(varIdRead -> True))) c,isVariadic) = do
    v' <- freshVarId (varIdBase v) Nothing
    t' <- substProxy "localTplt" ss False ssBounds t
    let i' = VarName t' $ VIden v'
    let ss' :: SubstsProxy GIdentifier (TcM m)
        ss' = substsProxyFromTSubsts l (TSubsts $ Map.singleton v (varNameToType i')) `appendSubstsProxy` ss
    let ssBounds' :: Map GIdentifier GIdentifier
        ssBounds' = Map.insert (VIden v) (VIden v') ssBounds
    c' <- substProxy "localTplt" ss' False ssBounds c
    return ((Constrained i' c',isVariadic),ss',ssBounds')
uniqueTyVar (l::loc) (ss::SubstsProxy GIdentifier (TcM m)) ssBounds (i,isVariadic) = return ((i,isVariadic),ss,ssBounds)

uniqueTyVars :: ProverK loc m => loc -> SubstsProxy GIdentifier (TcM m) -> Map GIdentifier GIdentifier -> [(Constrained Var,IsVariadic)] -> TcM m ([(Constrained Var,IsVariadic)],SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier)
uniqueTyVars l ss ssBounds [] = return ([],ss,ssBounds)
uniqueTyVars l ss ssBounds (x:xs) = do
    (x',ss',ssBounds') <- uniqueTyVar l ss ssBounds x
    (xs',ss'',ssBounds'') <- uniqueTyVars l ss' ssBounds' xs
    return (x' : xs',ss'',ssBounds'')
    
uniqueProcVar :: ProverK loc m => loc -> SubstsProxy GIdentifier (TcM m) -> Map GIdentifier GIdentifier -> (Bool,Var,IsVariadic) -> TcM m ((Bool,Var,IsVariadic),SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier)
-- refresh const variables
uniqueProcVar (l::loc) (ss::SubstsProxy GIdentifier (TcM m)) ssBounds (isConst,i@(VarName t (VIden v@(varIdRead -> True))),isVariadic) = do
    v' <- freshVarId (varIdBase v) Nothing
    t' <- substProxy "localTplt" ss False ssBounds t
    let i' = VarName t' $ VIden v'
    let ss' :: SubstsProxy GIdentifier (TcM m)
        ss' = substsProxyFromTSubsts l (TSubsts $ Map.singleton v (varNameToType i')) `appendSubstsProxy` ss
    let doConst = isConst || isVariadic
    let ssBounds' :: Map GIdentifier GIdentifier
        ssBounds' = if doConst then Map.insert (VIden v) (VIden v') ssBounds else ssBounds
    return ((isConst,i',isVariadic),ss',ssBounds')
uniqueProcVar (l::loc) (ss::SubstsProxy GIdentifier (TcM m)) ssBounds (isConst,i,isVariadic) = return ((isConst,i,isVariadic),ss,ssBounds)

uniqueProcVars :: ProverK loc m => loc -> SubstsProxy GIdentifier (TcM m) -> Map GIdentifier GIdentifier -> [(Bool,Var,IsVariadic)] -> TcM m ([(Bool,Var,IsVariadic)],SubstsProxy GIdentifier (TcM m),Map GIdentifier GIdentifier)
uniqueProcVars l ss ssBounds [] = return ([],ss,ssBounds)
uniqueProcVars l ss ssBounds (x:xs) = do
    (x',ss',ssBounds') <- uniqueProcVar l ss ssBounds x
    (xs',ss'',ssBounds'') <- uniqueProcVars l ss' ssBounds' xs
    return (x' : xs',ss'',ssBounds'')










