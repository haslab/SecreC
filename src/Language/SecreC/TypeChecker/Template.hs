{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Utils
import Language.SecreC.Pretty
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.TypeChecker.Environment
import {-# SOURCE #-} Language.SecreC.TypeChecker.Index

import Data.Typeable
import Data.Either
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Foldable

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Control.Monad.State as State

import Text.PrettyPrint

instance MonadIO m => Vars m [Expression VarIdentifier Type] where
    traverseVars f = mapM f
    
instance MonadIO m => Vars m [Cond (VarName VarIdentifier Type)] where
    traverseVars f = mapM f
    
instance PP [Expression VarIdentifier Type] where
    pp xs = parens $ sepBy comma $ map pp xs

instance PP [Cond (VarName VarIdentifier Type)] where
    pp xs = parens $ sepBy comma $ map pp xs

-- Procedure arguments are maybe provided with index expressions
-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: (VarsTcM loc,Location loc) => loc -> Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> TcM loc [EntryEnv loc] -> TcM loc (DecType,Maybe [VarName VarIdentifier Type])
matchTemplate l doCoerce n targs pargs ret check = do
    entries <- check
    instances <- instantiateTemplateEntries doCoerce n targs pargs ret entries
    let def = ppTpltApp n targs pargs ret
    vs <- do
        x <- fvIds n
        y1 <- fvIds targs
        y2 <- fvIds pargs
        z <- fvIds ret
        return $ Set.unions [x,y1,y2,z]
    let oks = rights instances
    let errs = lefts instances
    case oks of
        [] -> do
            let defs = map (\(e,err) -> (locpos $ entryLoc e,pp (entryType e),err)) errs
            ss <- liftM ppTSubsts (filterTSubsts vs =<< getTSubsts)
            tcError (locpos l) $ Halt $ NoMatchingTemplateOrProcedure def defs ss
        [(e,subst,rs)] -> do
            dec <- resolveTemplateEntry l n targs pargs ret e subst
            return (dec,rs)
        otherwise -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,subst,rs):_) <- sortByM (compareTemplateDecls def l n) oks
            -- guarantee that the most specific template can be fully instantiated
            addErrorM
                (TypecheckerError (locpos l) . Halt . TemplateSolvingError def)
                (prove l True (addHeadTDict subst))
            -- return the instantiated body of the most specific declaration
            dec <- resolveTemplateEntry l n targs pargs ret e subst
            return (dec,rs)

templateCstrs :: Location loc => Doc -> loc -> TDict loc -> TDict loc
templateCstrs doc p d = d { tCstrs = Map.map upd (tCstrs d) }
    where
    upd (Loc l k) = Loc p $ k { kCstr = DelayedK (kCstr k) (TypecheckerError (locpos p) . TemplateSolvingError doc) }

resolveTemplateEntry :: (VarsTcM loc,Location loc) => loc -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> EntryEnv loc -> TDict loc -> TcM loc DecType
resolveTemplateEntry p n targs pargs ret e dict = do
--    liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppr n ++ " " ++ ppr args ++ " " ++ ppr (entryType e)
    let l = entryLoc e
    addHeadTDict dict
    case entryType e of
        DecT (TpltType a b cstrs specs body) -> do
            let ppApp = quotes (ppTpltApp n targs pargs ret) 
            let cstrs' = fmap (updpos l) $ templateCstrs ppApp (locpos p) cstrs
--            doc <- ppConstraints cstrs'
--            liftIO $ putStrLn $ "constraints " ++ show doc
--            body' <- sub body
--            specs' <- sub specs
            cstrs'' <- liftM snd $ tcProve l False $ addHeadTDict cstrs'
            return $ TpltType a b (fmap locpos cstrs'') specs body
        DecT (ProcType a b n args body stmts) -> do
--            n' <- sub n
--            body' <- sub body
--            args' <- mapM sub args
--            stmts' <- sub stmts
            return $ ProcType a b n args body stmts
        t -> error $ "resolveTemplateEntry: " ++ show t

templateDecReturn :: (VarsTcM loc,Location loc) => loc -> DecType -> TcM loc Type
templateDecReturn l (TpltType _ _ _ _ b) = templateDecReturn l b
templateDecReturn l (ProcType _ _ _ _ r _) = return r
templateDecReturn l s@(StructType {}) = return $ BaseT $ TyDec s
templateDecReturn l (DVar v) = do
    d <- resolveDVar l v
    templateDecReturn l d

-- | Tells if one declaration is strictly more specific than another, and if not it fails.
-- Since we are unifying base types during instantiation, it may happen that the most specific match is chosen over another more generic best match. This problem does not arise though if we only resolve templates on full instantiation. If we ever change this, we should use instead a three-way comparison that also tries to minimize the number of instantiated type variables in the context.
-- An example is if we tried to match the template over a type variable T:
-- y = f ((T) x)
-- bool f (int x) { ... }     (1)
-- bool f (T x) { ... }       (2)
-- bool f (T [[N]] x) { ... } (3)
-- We would be choosing choosing (1), even though the best match is in principle (2), that does not instantiate T.
compareTemplateDecls :: (VarsTcM loc,Location loc) => Doc -> loc -> TIdentifier -> (EntryEnv loc,TDict loc,Maybe [VarName VarIdentifier Type]) -> (EntryEnv loc,TDict loc,Maybe [VarName VarIdentifier Type]) -> TcM loc Ordering
compareTemplateDecls def l n (e1,s1,rs1) (e2,d2,rs2) = tcBlock $ do
    State.modify $ \env -> env { localHyps = Set.empty, globalHyps = Set.empty }
    e1' <- localTemplate e1
    e2' <- localTemplate e2
    (targs1,pargs1,ret1) <- templateArgs n e1'
    (targs2,pargs2,ret2) <- templateArgs n e2'
    let defs = map (\e -> (locpos $ entryLoc e,pp (entryType e))) [e1,e2]
    let err = TypecheckerError (locpos l) . Halt . ConflictingTemplateInstances def defs
    ord <- addErrorM err $ do
        addTemplateConds e1'
        addTemplateConds e2'
        let comparePArg (Cond v1@(VarName t1 n1) c1) (Cond v2@(VarName t2 n2) c2) = do
            let e1 = RVariablePExpr t1 v1
            let e2 = RVariablePExpr t2 v2
            unifiesExpr l e1 e2
            tryAddHypothesis l LocalScope $ HypEqual e1 e2
            compares l t1 t2
            comparesSCond l (maybe trueSCond id c1) (maybe trueSCond id c2)
        ord2 <- liftM mconcat $ constraintList ComparisonException comparePArg l (concat pargs1) (concat pargs2)
        ord3 <- comparesList l (maybeToList ret1) (maybeToList ret2)
        return $ mconcat [ord2,ord3]
    when (ord == EQ) $ do
        ss <- liftM ppTSubsts getTSubsts
        tcError (locpos l) $ DuplicateTemplateInstances def defs ss
    return ord

addTemplateConds :: (Vars (TcM loc) loc,Location loc) => EntryEnv loc -> TcM loc ()
addTemplateConds e = case entryType e of
    DecT (TpltType tpltid args cstrs specials body) -> do
        forM_ args $ \(Cond v c) -> case c of
            Nothing -> return ()
            Just ex -> tryAddHypothesis (entryLoc e) LocalScope $ HypCondition ex
    otherwise -> return ()
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (VarsTcM loc,Location loc) => Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> [EntryEnv loc] -> TcM loc [Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc,Maybe [VarName VarIdentifier Type])]
instantiateTemplateEntries doCoerce n targs pargs ret es = mapM (instantiateTemplateEntry doCoerce n targs pargs ret) es

instantiateTemplateEntry :: (VarsTcM loc,Location loc) => Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> EntryEnv loc -> TcM loc (Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc,Maybe [VarName VarIdentifier Type]))
instantiateTemplateEntry doCoerce n targs pargs ret e = do
    let l = entryLoc e
    e' <- localTemplate e
    --liftIO $ putStrLn $ "instantiating " ++ ppr n ++ " " ++ ppr targs ++ " " ++ ppr pargs ++ " " ++ ppr ret ++ " " ++ ppr (entryType e')
    (tplt_targs,tplt_pargs,tplt_ret) <- templateArgs n e'
    let matchName = unifiesTIdentifier l (templateIdentifier $ entryType e') n -- reverse unification
    let proof = do
                    -- if the instantiation has explicit template arguments, unify them with the base template
                    when (isJust $ targs) $ unifiesList l (concat tplt_targs) (concat targs) -- reverse unification
                    -- coerce procedure arguments into the base procedure arguments
                    let coercePArg e (Cond v2@(VarName tt n2) c) = do
                        let t = loc e
                        e2 <- if doCoerce
                            then coercesE l e t tt
                            else unifies l t tt >> return e
                        -- add the procedure argument to the environment
                        addValueM l v2 e2
                        tryAddHypothesis l LocalScope $ HypAssign (VarName tt n2) e2
                    constraintList CoercionException coercePArg l (concat pargs) (concat tplt_pargs)
                    -- unify the procedure return type
                    unifiesList l (maybeToList tplt_ret) (maybeToList ret) -- reverse unification
    ok <- newErrorM $ proveWith l False (matchName >> proof)
    case ok of
        Left err -> return $ Left (e',err)
        Right ((),subst) -> do
--            liftIO $ putStrLn $ "entry " ++ ppr (entryType e) ++ "\n" ++ ppr subst
--            liftIO $ putStrLn $ "instantiated " ++ ppr n ++ " " ++ ppr args ++ " " ++ ppr ret ++ " " ++ ppr (entryType e') ++ "\n" ++ show ss ++  "INST\n" ++ ppr (tSubsts subst) 
            return $ Right (e',subst,fmap (map unCond) tplt_pargs)

templateIdentifier :: Type -> TIdentifier
templateIdentifier (DecT t) = templateIdentifier' t
    where
    templateIdentifier' :: DecType -> TIdentifier
    templateIdentifier' (TpltType _ _ _ _ t) = templateIdentifier' t
    templateIdentifier' (ProcType _ _ n _ _ _) = Right n
    templateIdentifier' (StructType _ _ n _) = Left n
        
-- | Extracts a head signature from a template type declaration (template arguments,procedure arguments, procedure return type)
templateArgs :: Location loc => TIdentifier -> EntryEnv loc -> TcM loc (Maybe [Type],Maybe [Cond (VarName VarIdentifier Type)],Maybe Type)
templateArgs (Left name) e = case entryType e of
    DecT (TpltType _ args cstrs [] body) -> do -- a base template uses the base arguments
        return (Just $ map condVarNameToType args,Nothing,Nothing)
    DecT (TpltType _ args cstrs specials body) -> do -- a specialization uses the specialized arguments
        return (Just specials,Nothing,Nothing)
templateArgs (Right name) e = case entryType e of
    DecT (TpltType _ args cstrs [] (ProcType _ _ n vars ret stmts)) -> do -- include the return type
        return (Just $ map condVarType args,Just vars,Just ret)
    DecT (ProcType _ _ n vars ret stmts) -> do -- include the return type
        return (Nothing,Just vars,Just ret)
    otherwise -> genTcError (locpos $ entryLoc e) $ text "Invalid type for procedure template"

condVarType (Cond (VarName t n) c) = condType t c
condVar (Cond (VarName t n) c) = VarName (condType t c) n

-- | renames the variables in a template to local names
localTemplate :: (VarsTcM loc,Location loc) => EntryEnv loc -> TcM loc (EntryEnv loc)
localTemplate (e::EntryEnv loc) = case entryType e of
    DecT (TpltType tpltid args cstrs specials body) -> do
        (args',uniqs) <- uniqueVars Map.empty args
        let sub :: Vars (TcM loc) a => a -> TcM loc a
            sub = substFromTSubsts l uniqs
        body' <- sub body
        cstrs' <- sub cstrs
        specials' <- sub specials
        let t' = DecT $ TpltType tpltid args' cstrs' specials' body'
        v' <- sub (entryValue e)
        return $ EntryEnv l t' v'
    DecT t -> return e
  where
    uniqueVar :: TSubsts -> Cond (VarName VarIdentifier Type) -> TcM loc (Cond (VarName VarIdentifier Type),TSubsts)
    uniqueVar ss (Cond i@(VarName t v) c) = do
        j <- newTyVarId
        let i' = VarName t (VarIdentifier (varIdBase v) (Just j) False)
        let ss' = Map.insert (VarName () v) (varNameToType i') ss
        c' <- substFromTSubsts l ss' c
        return (Cond i' c',ss')
    uniqueVars :: TSubsts -> [Cond (VarName VarIdentifier Type)] -> TcM loc ([Cond (VarName VarIdentifier Type)],TSubsts)
    l = entryLoc e
    uniqueVars ss [] = return ([],ss)
    uniqueVars ss (x:xs) = do
        (x',ss') <- uniqueVar ss x
        (xs',ss'') <- uniqueVars ss' xs
        return (x':xs',ss'')










