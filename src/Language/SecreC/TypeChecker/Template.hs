{-# LANGUAGE ViewPatterns, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Utils as Utils
import Language.SecreC.Pretty
import Language.SecreC.Position
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

instance MonadIO m => Vars VarIdentifier m [Expression VarIdentifier Type] where
    traverseVars f = mapM f
    
instance MonadIO m => Vars VarIdentifier m [(Bool,Cond (VarName VarIdentifier Type))] where
    traverseVars f = mapM f
    
instance PP [Expression VarIdentifier Type] where
    pp xs = parens $ sepBy comma $ map pp xs

instance PP [(Bool,Cond (VarName VarIdentifier Type))] where
    pp xs = parens $ sepBy comma $ map (\(x,y) -> ppConst x <+> pp y) xs

-- Procedure arguments are maybe provided with index expressions
-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> TcM loc m [EntryEnv loc] -> TcM loc m (DecType,[VarName VarIdentifier Type])
matchTemplate l doCoerce n targs pargs ret check = do
    entries <- check
    instances <- instantiateTemplateEntries doCoerce n targs pargs ret entries
    let oks = rights instances
    let errs = lefts instances
    def <- ppTpltAppM l n targs pargs ret
    case oks of
        [] -> do
            defs <- forM errs $ \(e,err) -> do
                t' <- ppM l $ entryType e
                return (locpos $ entryLoc e,t',err)
            tcError (locpos l) $ Halt $ NoMatchingTemplateOrProcedure def defs
        [(e,subst,rs)] -> do
            dec <- resolveTemplateEntry l n targs pargs ret e subst
            return (dec,rs)
        otherwise -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,subst,rs):_) <- sortByM (compareTemplateDecls def l n) oks
            -- return the instantiated body of the most specific declaration
            dec <- resolveTemplateEntry l n targs pargs ret e subst
            return (dec,rs)

templateCstrs :: Location loc => (Int,SecrecErrArr) -> Doc -> loc -> TDict loc -> TDict loc
templateCstrs (i,arr) doc p d = d { tCstrs = Map.map upd (tCstrs d) }
    where
    upd (Loc l k) = Loc l $ k { kCstr = DelayedK (kCstr k) (succ i,arr . TypecheckerError (locpos p) . TemplateSolvingError doc) }
    
dependentCstrs :: Location loc => loc -> [IOCstr] -> TDict loc -> TDict loc
dependentCstrs l deps dict = dict { tCstrs = Map.map (fmap f) (tCstrs dict) }
    where
    f :: IOCstr -> IOCstr
    f (IOCstr k st) = IOCstr (DepK (Set.fromList deps) k) st

resolveTemplateEntry :: (VarsIdTcM loc m,Location loc) => loc -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> EntryEnv loc -> TDict loc -> TcM loc m DecType
resolveTemplateEntry p n targs pargs ret e dict = do
--    liftIO $ putStrLn $ "resolveTemplateEntry " ++ ppr n ++ " " ++ ppr args ++ " " ++ ppr (entryType e)
    def <- ppTpltAppM p n targs pargs ret
    -- guarantee that the most specific template can be fully instantiated
    arr <- askErrorM'
    prove p False $ addHeadTDict $ templateCstrs arr def p dict
    case entryType e of
        DecT dec -> return dec
        t -> genTcError (locpos p) $ text "resolveTemplateEntry: not a declaration type" <+> pp t

templateDecReturn :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> TcM loc m Type
templateDecReturn l (TpltType _ _ _ _ _ b) = templateDecReturn l b
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
compareTemplateDecls :: (VarsIdTcM loc m,Location loc) => Doc -> loc -> TIdentifier -> (EntryEnv loc,TDict loc,[VarName VarIdentifier Type]) -> (EntryEnv loc,TDict loc,[VarName VarIdentifier Type]) -> TcM loc m Ordering
compareTemplateDecls def l n (e1,_,_) (e2,_,_) = tcBlock $ do
    State.modify $ \env -> env { localHyps = Set.empty, globalHyps = Set.empty }
    e1' <- localTemplate e1
    e2' <- localTemplate e2
    (targs1,pargs1,ret1) <- templateArgs n e1'
    (targs2,pargs2,ret2) <- templateArgs n e2'
    let defs = map (\e -> (locpos $ entryLoc e,pp (entryType e))) [e1,e2]
    let err = TypecheckerError (locpos l) . Halt . ConflictingTemplateInstances def defs
    ord <- addErrorM l err $ do
        addTemplateConds e1'
        addTemplateConds e2'
        let comparePArg (_,Cond v1@(VarName t1 n1) c1) (_,Cond v2@(VarName t2 n2) c2) = do
            let e1 = varExpr v1
            let e2 = varExpr v2
            unifiesExpr l e1 e2
            tryAddHypothesis l LocalScope $ HypEqual e1 e2
            o1 <- compares l t1 t2
            o2 <- comparesSCond l (maybe trueSCond id c1) (maybe trueSCond id c2)
            return $ mconcat [o1,o2]
        ord2 <- liftM mconcat $ constraintList (ComparisonException "procedure argument") comparePArg l (concat pargs1) (concat pargs2)
        ord3 <- comparesList l (maybeToList ret1) (maybeToList ret2)
        return $ mconcat [ord2,ord3]
    when (ord == EQ) $ do
        tcError (locpos l) $ DuplicateTemplateInstances def defs
    return ord

addTemplateConds :: (VarsIdTcM loc m,Location loc) => EntryEnv loc -> TcM loc m ()
addTemplateConds e = case entryType e of
    DecT (TpltType tpltid args cstrs specials frees body) -> do
        forM_ args $ \(Cond v c) -> case c of
            Nothing -> return ()
            Just ex -> tryAddHypothesis (entryLoc e) LocalScope $ HypCondition ex
    otherwise -> return ()
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (VarsIdTcM loc m,Location loc) => Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> [EntryEnv loc] -> TcM loc m [Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc,[VarName VarIdentifier Type])]
instantiateTemplateEntries doCoerce n targs pargs ret es = mapM (instantiateTemplateEntry doCoerce n targs pargs ret) es

instantiateTemplateEntry :: (VarsIdTcM loc m,Location loc) => Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> EntryEnv loc -> TcM loc m (Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc,[VarName VarIdentifier Type]))
instantiateTemplateEntry doCoerce n targs pargs ret e = tcBlock $ do
    let l = entryLoc e
    e' <- localTemplate e
--    liftIO $ putStrLn $ "instantiating " ++ ppr n ++ " " ++ ppr targs ++ " " ++ ppr pargs ++ " " ++ ppr ret ++ " " ++ ppr (entryType e')
    (tplt_targs,tplt_pargs,tplt_ret) <- templateArgs n e'
    let matchName = unifiesTIdentifier l (templateIdentifier $ entryType e') n -- reverse unification
    let proof = do
                    -- if the instantiation has explicit template arguments, unify them with the base template
                    when (isJust targs) $ unifiesList l (concat $ fmap (map unCond) tplt_targs) (concat targs) -- reverse unification
                    -- coerce procedure arguments into the base procedure arguments
                    let coercePArg e cond@(isCond,Cond v2@(VarName tt n2) c) = do
                        let t = loc e
                        --liftIO $ putStrLn $ "coercePArg " ++ show (pp e <+> text "::" <+> pp t) ++ " " ++ show (ppCond (\(VarName t x) -> pp x <+> text "::" <+> pp t) cond)
                        x2 <- newTypedVar "pa" tt
                        if doCoerce
                            then tcCstrM l $ Coerces e t x2 tt
                            else do
                                tcCstrM l $ Unifies t tt
                                tcCstrM l $ Unifies (IdxT $ varExpr x2) (IdxT e)
                        when isCond $ do
                            tcCstrM l $ Unifies (IdxT $ varExpr v2) (IdxT $ varExpr x2)
                            tryAddHypothesis l LocalScope $ HypAssign (VarName tt n2) (varExpr x2)
                            case c of
                                Nothing -> return ()
                                Just i -> do
                                    ic <- expr2ICond $ fmap (Typed l) i
                                    checkCstrM l $ IsValid ic
                        return x2
                    xs <- constraintList (CoercionException "procedure argument") coercePArg l (concat pargs) (concat tplt_pargs)
                    -- satisfy the template argument invariants
                    forM_ (maybe [] (catMaybes . map (\(Cond x c) -> c)) tplt_targs) $ \c -> do
                        ic <- expr2ICond $ fmap (Typed l) c
                        checkCstrM l $ IsValid ic
                    -- unify the procedure return type
                    unifiesList l (maybeToList tplt_ret) (maybeToList ret) -- reverse unification
                    return xs
    ok <- newErrorM $ proveWith l False (matchName >> proof)
    case ok of
        Left err -> return $ Left (e',err)
        Right (xs,subst) -> do
            let depCstrs = dependentCstrs l (map unLoc $ Map.elems $ tCstrs $ subst) (templateTDict e')
            return $ Right (e',subst `mappend` depCstrs,xs)

templateIdentifier :: Type -> TIdentifier
templateIdentifier (DecT t) = templateIdentifier' t
    where
    templateIdentifier' :: DecType -> TIdentifier
    templateIdentifier' (TpltType _ _ _ _ _ t) = templateIdentifier' t
    templateIdentifier' (ProcType _ _ n _ _ _) = Right n
    templateIdentifier' (StructType _ _ n _) = Left n
        
-- | Extracts a head signature from a template type declaration (template arguments,procedure arguments, procedure return type)
templateArgs :: (MonadIO m,Location loc) => TIdentifier -> EntryEnv loc -> TcM loc m (Maybe [Cond Type],Maybe [(Bool,Cond (VarName VarIdentifier Type))],Maybe Type)
templateArgs (Left name) e = case entryType e of
    DecT (TpltType _ args cstrs [] frees body) -> do -- a base template uses the base arguments
        return (Just $ map (fmap varNameToType) args,Nothing,Nothing)
    DecT (TpltType _ args cstrs specials frees body) -> do -- a specialization uses the specialized arguments
        return (Just $ map (flip Cond Nothing) specials,Nothing,Nothing)
templateArgs (Right name) e = case entryType e of
    DecT (TpltType _ args cstrs [] frees (ProcType _ _ n vars ret stmts)) -> do -- include the return type
        return (Just $ map (fmap varNameToType) args,Just vars,Just ret)
    DecT (ProcType _ _ n vars ret stmts) -> do -- include the return type
        return (Nothing,Just vars,Just ret)
    otherwise -> genTcError (locpos $ entryLoc e) $ text "Invalid type for procedure template"

templateTDict :: Location loc => EntryEnv loc -> TDict loc
templateTDict e = case entryType e of
    DecT (TpltType _ _ d _ _ _) -> fmap (updpos (entryLoc e)) d
    otherwise -> mempty

condVarType (Cond (VarName t n) c) = condType t c
condVar (Cond (VarName t n) c) = VarName (condType t c) n

-- | renames the variables in a template to local names
localTemplate :: (VarsIdTcM loc m,Location loc) => EntryEnv loc -> TcM loc m (EntryEnv loc)
localTemplate e = case entryType e of
    DecT t -> do
        t' <- localTemplateType Proxy (entryLoc e) t
        return $ EntryEnv (entryLoc e) $ DecT t'

localTemplateType :: (VarsIdTcM loc m,Location loc) => Proxy m -> loc -> DecType -> TcM loc m DecType
localTemplateType (m::Proxy m) (l::loc) et = case et of
    TpltType tpltid args cstrs specials frees body -> do
        (frees',freelst) <- Utils.mapAndUnzipM freeVar $ Set.toList frees
        (args',uniqs) <- uniqueVars Map.empty args
        let ss :: SubstsProxy VarIdentifier (TcM loc m)
            ss = substsFromTSubsts l uniqs `appendSubstsProxy` substsProxyFromList freelst
        body' <- substProxy ss body
        cstrs' <- substProxy ss cstrs
        specials' <- substProxy ss specials
        body'' <- localTemplateType m l body'
        return $ TpltType tpltid args' cstrs' specials' (Set.fromList frees') body''
    ProcType tpltid p pid (unzip -> (isConsts,args)) ret stmts -> do
        (args',uniqs) <- uniqueVars Map.empty args
        let ss :: SubstsProxy VarIdentifier (TcM loc m)
            ss = substsFromTSubsts l uniqs
        ret' <- substProxy ss ret
        stmts' <- substProxy ss stmts
        return $ ProcType tpltid p pid (zip isConsts args') ret' stmts'
    otherwise -> return et
  where
    freeVar v = do
        j <- newTyVarId
        let v' = v { varIdUniq = Just j }
        return (v',(v,v'))
    uniqueVar ss (Cond i@(VarName t v) c) = do
        j <- newTyVarId
        let i' = VarName t (VarIdentifier (varIdBase v) (Just j) False )
        let ss' = Map.insert v (varNameToType i') ss
        c' <- substFromTSubsts l ss' c
        return (Cond i' c',ss')
    uniqueVars ss [] = return ([],ss)
    uniqueVars ss (x:xs) = do
        (x',ss') <- uniqueVar ss x
        (xs',ss'') <- uniqueVars ss' xs
        return (x':xs',ss'')










