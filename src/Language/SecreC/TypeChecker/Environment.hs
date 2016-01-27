{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, GeneralizedNewtypeDeriving, ViewPatterns, StandaloneDeriving, GADTs, ScopedTypeVariables, TupleSections, FlexibleInstances, TypeFamilies, DeriveDataTypeable, DeriveFunctor #-}

module Language.SecreC.TypeChecker.Environment where

import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Monad
import Language.SecreC.Syntax
import Language.SecreC.Utils
import Language.SecreC.Error
import Language.SecreC.Pretty
import Language.SecreC.Vars
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Type
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import {-# SOURCE #-} Language.SecreC.TypeChecker.Index
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint

import Data.IORef
import Data.Int
import Data.Word
import Data.Unique
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Generics hiding (GT)
import Data.Dynamic
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Bifunctor

import Data.Graph.Inductive              as Graph
import Data.Graph.Inductive.Graph        as Graph
import Data.Graph.Inductive.PatriciaTree as Graph
import Data.Graph.Inductive.Query.DFS    as Graph

import Control.Applicative
import Control.Monad.State as State
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding ((<>))
import Control.Monad.Trans.RWS (RWS(..),RWST(..))
import qualified Control.Monad.Trans.RWS as RWS
import Control.Monad.Except

import System.IO.Unsafe
import Unsafe.Coerce

import Safe

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as Pretty

import qualified Data.HashTable.Weak.IO as WeakHash
import qualified System.Mem.Weak.Map as WeakMap

import System.Mem.Weak.Exts as Weak

-- | Gets the variables of a given type class
getVars :: (MonadIO m,Location loc) => Scope -> TypeClass -> TcM loc m (Map VarIdentifier (Bool,EntryEnv loc))
getVars GlobalScope c = do
    vs <- liftM globalVars State.get
    return $ Map.filter (\(_,e) -> typeClass "getVarsG" (entryType e) == c) vs
getVars LocalScope c = do
    vs <- liftM vars State.get
    return $ Map.filterWithKey (\k (_,e) -> typeClass ("getVarsL " ++ ppr k ++ ppr (locpos $ entryLoc e)) (entryType e) == c) vs

addVar :: (MonadIO m,Location loc) => Scope -> VarIdentifier -> Bool -> EntryEnv loc -> TcM loc m ()
addVar GlobalScope n b e = modify $ \env -> env { globalVars = Map.insert n (b,e) (globalVars env) }
addVar LocalScope n b e = modify $ \env -> env { localVars = Map.insert n (b,e) (localVars env) }

addFree n = modify $ \env -> env { localFrees = Set.insert n (localFrees env) }

getFrees :: (Monad m,Location loc) => TcM loc m (Set VarIdentifier)
getFrees = liftM localFrees State.get

-- replaces a constraint in the constraint graph by a constraint graph
replaceCstrWithGraph :: (MonadIO m,Location loc) => loc -> Int -> Set Int -> IOCstrGraph loc -> Set Int -> TcM loc m ()
replaceCstrWithGraph l kid ins gr outs = do
    updateHeadTDict $ \d -> return ((),d { tCstrs = delNode kid (tCstrs d) })
    buildGraph l ins gr outs

---- replaces a constraint in the constraint graph by a constraint cluster
--replaceCstrWithCluster :: (MonadIO m,Location loc) => loc -> Int -> Set Int -> IOCstrGraph loc -> Set Int -> TcM loc m IOCstr
--replaceCstrWithCluster l kid ins gr outs = do
--    updateHeadTDict $ \d -> return ((),d { tCstrs = delNode kid (tCstrs d) })
--    buildCluster l ins gr outs

buildGraph :: (MonadIO m,Location loc) => loc -> Set Int -> IOCstrGraph loc -> Set Int -> TcM loc m ()
buildGraph l ins gr outs = do
    -- the cluster only depends on the hypotheses
    forM_ (flattenIOCstrGraph gr) $ \iok -> addIOCstrDependenciesM ins iok outs

--tcCluster :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m a -> TcM loc m a
--tcCluster l m = do
--    hyps <- getHyps
--    (x,d) <- tcWith l m
--    addHeadTDict $ d { tCstrs = Graph.empty }
--    iok <- buildCluster l (mapSet (ioCstrId . unLoc) hyps) (tCstrs d) Set.empty
----    liftIO $ putStrLn $ "tcCluster: " ++ ppr iok
--    return x

withHypotheses :: MonadIO m => Scope -> TcM loc m a -> TcM loc m a
withHypotheses LocalScope m = do
    env <- State.get
    let l = localHyps env
    x <- m
    State.modify $ \env -> env { localHyps = l }
    return x
withHypotheses GlobalScope m = do
    env <- State.get
    let l = localHyps env
    let g = globalHyps env
    x <- m
    State.modify $ \env -> env { localHyps = l, globalHyps = g }
    return x

checkVariable :: (MonadIO m,Location loc) => Bool -> Scope -> VarName VarIdentifier loc -> TcM loc m (VarName VarIdentifier (Typed loc))
checkVariable isCond scope (VarName l n) = do
    vs <- getVars scope TypeC
    case Map.lookup n vs of
        Just (b,e) -> do
            when (isCond && b) $ tcError (locpos l) $ AssignConstVariable (pp n)
            return $ VarName (Typed l $ entryType e) n
        Nothing -> tcError (locpos l) $ VariableNotFound (pp n)

-- | Adds a new variable to the environment
newVariable :: (MonadIO m,VarsIdTcM loc m,Location loc) => Scope -> VarName VarIdentifier (Typed loc) -> Maybe (Expression VarIdentifier (Typed loc)) -> Bool -> TcM loc m ()
newVariable scope v@(VarName (Typed l t) n) val isCond = do
    vars <- getVars scope TypeC
    case Map.lookup n vars of
        Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
        Nothing -> return ()
    addVar scope n isCond (EntryEnv l t)
    case scope of
        LocalScope -> addFree n
        otherwise -> return ()
    case val of
        Just e -> do
            tcCstrM l $ Unifies (IdxT $ fmap typed $ varExpr v) (IdxT $ fmap typed e)
        Nothing -> return ()

addHypDependencies :: (Monad m,Location loc) => loc -> Hyps loc -> IOCstr -> TcM loc m ()
addHypDependencies l hyps iok = do
    addIOCstrDependenciesM (mapSet (ioCstrId . unLoc) hyps) (Loc l iok) Set.empty

addHypothesis :: (MonadIO m,Location loc) => Scope -> Loc loc IOCstr -> TcM loc m ()
addHypothesis GlobalScope hyp = modify $ \env -> env { globalHyps = Set.insert hyp (globalHyps env) }
addHypothesis LocalScope hyp = modify $ \env -> env { localHyps = Set.insert hyp (localHyps env) }

tryAddCondHypothesis :: (VarsIdTcM loc m,Location loc) => loc -> Scope -> Maybe (SCond VarIdentifier Type) -> TcM loc m ()
tryAddCondHypothesis l scope Nothing = return ()
tryAddCondHypothesis l scope (Just c) = do
    deps <- getVarOutSet c
    tryAddHypothesis l scope deps (HypCondition c)

tryAddHypothesis :: (MonadIO m,Location loc) => loc -> Scope -> Set IOCstr -> HypCstr -> TcM loc m ()
tryAddHypothesis l scope deps hyp = do
    iok <- updateHeadTDict $ \d -> insertTDictCstr l (HypK hyp) Unevaluated d
--    iok <- liftIO $ newIOCstr (HypK hyp) Unevaluated
    addHypothesis scope $ Loc l iok
    addIOCstrDependenciesM (mapSet ioCstrId deps) (Loc l iok) Set.empty

-- | Adds a new domain variable to the environment
newDomainVariable :: (MonadIO m,Location loc) => Scope -> DomainName VarIdentifier (Typed loc) -> TcM loc m ()
newDomainVariable scope (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ InvalidDomainVariableName (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            vars <- getVars scope KindC
            case Map.lookup n vars of
                Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
                Nothing -> addVar scope n False (EntryEnv l t)

-- | Adds a new type variable to the environment
newTypeVariable :: (MonadIO m,Location loc) => Scope -> TypeName VarIdentifier (Typed loc) -> TcM loc m ()
newTypeVariable scope (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (b,es) -> tcError (locpos l) $ InvalidTypeVariableName (ppVarId n) (map (locpos . entryLoc) (b:Map.elems es))
        Nothing -> do
            vars <- getVars scope TypeStarC
            case Map.lookup n vars of
                Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
                Nothing -> addVar scope n False (EntryEnv l t)

-- | Adds a new domain to the environment
newDomain :: (MonadIO m,Location loc) => DomainName VarIdentifier (Typed loc) -> TcM loc m ()
newDomain (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ MultipleDefinedDomain (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t
            modify $ \env -> env { domains = Map.insert n e (domains env) }

-- | Checks if a domain exists in scope, and returns its type
-- Searches for both user-defined private domains and domain variables
checkDomain :: (MonadIO m,Location loc) => DomainName VarIdentifier loc -> TcM loc m Type
checkDomain (DomainName l n) = do
    ds <- liftM domains State.get
    case Map.lookup n ds of
        Just e -> case entryType e of
            SType (PrivateKind (Just k)) -> return $ SecT $ Private (DomainName () n) k
            otherwise -> genTcError (locpos l) $ text "Unexpected domain" <+> quotes (pp n) <+> text "without kind."
        Nothing -> do
            dvars <- getVars LocalScope KindC
            case Map.lookup n dvars of
                Just (_,e) -> return $ varNameToType $ VarName (entryType e) n
                Nothing -> tcError (locpos l) $ NotDefinedDomain (ppVarId n)

-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: (MonadIO m,Location loc) => TypeName VarIdentifier loc -> TcM loc m ([EntryEnv loc])
checkType (TypeName l n) = do
    ss <- liftM structs State.get
    case Map.lookup n ss of
        Just (base,es) -> return (base : Map.elems es)
        Nothing -> do
            vars <- getVars LocalScope TypeStarC
            case Map.lookup n vars of
                Just (_,e) -> return [ e { entryType = varNameToType (VarName (entryType e) n) } ] -- return the type variable
                Nothing -> tcError (locpos l) $ NotDefinedType (pp n)

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkNonTemplateType :: (MonadIO m,Location loc) => TypeName VarIdentifier loc -> TcM loc m Type
checkNonTemplateType tn@(TypeName l n) = do
    es <- checkType tn
    case es of
        [e] -> case entryType e of
            DecT d -> return $ BaseT $ TyDec d
            t -> return t
        es -> tcError (locpos l) $ NoNonTemplateType (pp n)

-- | Checks if a template type exists in scope
-- Returns all template type declarations in scope, base template first
checkTemplateType :: (MonadIO m,Location loc) => TypeName VarIdentifier loc -> TcM loc m [EntryEnv loc]
checkTemplateType ty@(TypeName _ n) = do
    (es) <- checkType ty
    let check e = unless (isStructTemplate $ entryType e) $ tcError (locpos $ loc ty) $ NoTemplateType (pp n) (locpos $ entryLoc e) (pp $ entryType e)
    mapM_ check es
    return (es)

-- | Checks if a variable argument of a template exists in scope
-- The argument can be a (user-defined or variable) type, a (user-defined or variable) domain or a dimension variable
checkTemplateArg :: (MonadIO m,Location loc) => TemplateArgName VarIdentifier loc -> TcM loc m (TemplateArgName VarIdentifier (Typed loc))
checkTemplateArg (TemplateArgName l n) = do
    env <- State.get
    let ss = structs env
    let ds = domains env
    let vs = vars env
    case (Map.lookup n ss,Map.lookup n ds,Map.lookup n vs) of
        (Just (base,es),Nothing,Nothing) -> case (base:Map.elems es) of
            [e] -> if (isStructTemplate $ entryType e)
                then tcError (locpos l) $ NoNonTemplateType (pp n)
                else return $ TemplateArgName (Typed l $ entryType e) n
            es -> tcError (locpos l) $ NoNonTemplateType (pp n)
        (Nothing,Just e,Nothing) -> case entryType e of
            SType (PrivateKind (Just k)) -> return $ TemplateArgName (Typed l $ SecT $ Private (DomainName () n) k) n
            otherwise -> genTcError (locpos l) $ text "Unexpected domain" <+> quotes (pp n) <+> text "without kind."
        (Nothing,Nothing,Just (b,e)) -> return $ TemplateArgName (Typed l $ varNameToType $ VarName (entryType e) n) n
        (mb1,mb2,mb3) -> tcError (locpos l) $ AmbiguousName (pp n) $ map (locpos . entryLoc) $ maybe [] (\(b,es) -> b:Map.elems es) (mb1) ++ maybeToList (mb2) ++ maybeToList (fmap snd mb3)

-- | Checks that a kind exists in scope
checkKind :: (MonadIO m,Location loc) => KindName VarIdentifier loc -> TcM loc m ()
checkKind (KindName l n) = do
    ks <- liftM kinds State.get
    case Map.lookup n ks of
        Just e -> return ()
        Nothing -> tcError (locpos l) $ NotDefinedKind (ppVarId n)

-- | Adds a new kind to the environment
newKind :: (MonadIO m,Location loc) => KindName VarIdentifier (Typed loc) -> TcM loc m ()
newKind (KindName (Typed l t) n) = do
    ks <- liftM kinds get
    case Map.lookup n ks of
        Just e -> tcError (locpos l) $ MultipleDefinedKind (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t
            modify $ \env -> env { kinds = Map.insert n e (kinds env) } 

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: (VarsIdTcM loc m,Location loc) => [Cond (VarName VarIdentifier Type)] -> Op VarIdentifier (Typed loc) -> TcM loc m ()
addTemplateOperator vars op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    let o = funit op
    solve l
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    frees <- getFrees
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] frees d)
    liftIO $ putStrLn $ "addTemplateOp " ++ ppr (entryType e)
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (VarsIdTcM loc m,Location loc) => Op VarIdentifier (Typed loc) -> TcM loc m ()
newOperator op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    i <- case decTypeTyVarId d of
        Just i -> return i
        otherwise -> genTcError (locpos l) $ text "Unresolved declaration for operator" <+> pp op
    let o = funit op
    let e = EntryEnv l t
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
  
 -- | Checks that an operator exists.
checkOperator :: (VarsIdTcM loc m,Location loc) => Op VarIdentifier loc -> TcM loc m [EntryEnv loc]
checkOperator op@(OpCast l t) = do
    ps <- liftM operators State.get
    let cop = funit op
    -- select all cast declarations
    let casts = concatMap Map.elems $ Map.elems $ Map.filterWithKey (\k v -> isJust $ isOpCast k) ps
    return casts
checkOperator op = do
    ps <- liftM operators State.get
    let cop = funit op
    case Map.lookup cop ps of
        Nothing -> tcError (locpos $ loc op) $ Halt $ NotDefinedOperator $ pp cop
        Just es -> return $ Map.elems es
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: (VarsIdTcM loc m,Location loc) => [Cond (VarName VarIdentifier Type)] -> ProcedureName VarIdentifier (Typed loc) -> TcM loc m ()
addTemplateProcedure vars (ProcedureName (Typed l t) n) = do
    dt <- typeToDecType l t
    solve l
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    frees <- getFrees
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] frees dt)
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: (VarsIdTcM loc m,Location loc) => ProcedureName VarIdentifier (Typed loc) -> TcM loc m ()
newProcedure (ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    i <- case decTypeTyVarId d of
        Just i -> return i
        otherwise -> genTcError (locpos l) $ text "Unresolved declaration for procedure" <+> quotes (pp n)
    let e = EntryEnv l t
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
  
 -- | Checks that a procedure exists.
checkProcedure :: (MonadIO m,Location loc) => ProcedureName VarIdentifier loc -> TcM loc m [EntryEnv loc]
checkProcedure (ProcedureName l n) = do
    ps <- liftM procedures State.get
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ Halt $ NotDefinedProcedure (ppVarId n)
        Just es -> return $ Map.elems es
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (VarsIdTcM loc m,Location loc) => [Cond (VarName VarIdentifier Type)] -> TypeName VarIdentifier (Typed loc) -> TcM loc m ()
addTemplateStruct vars (TypeName (Typed l t) n) = do
    struct <- typeToDecType l t
    solve l
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    frees <- getFrees
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] frees struct)
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate (ppVarId n) (locpos $ loc base)
        Nothing -> modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: (VarsIdTcM loc m,Location loc) => [Cond (VarName VarIdentifier Type)] -> [Type] -> TypeName VarIdentifier (Typed loc) -> TcM loc m ()
addTemplateStructSpecialization vars specials (TypeName (Typed l t) n) = do
    struct <- typeToDecType l t
    solve l
    cstrs <- liftM (headNe . tDict) State.get
    i <- newTyVarId
    frees <- getFrees
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) specials frees struct)
    let mergeStructs (b1,s1) (b2,s2) = (b2,s1 `Map.union` s2)
    modify $ \env -> env { structs = Map.update (\(b,s) -> Just (b,Map.insert i e s)) n (structs env) }

-- | Defines a new struct type
newStruct :: (MonadIO m,Location loc) => TypeName VarIdentifier (Typed loc) -> TcM loc m ()
newStruct (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStruct (ppVarId n) (locpos $ entryLoc base)
        Nothing -> do
            let e = EntryEnv l t
            modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }

addSubstsM :: (MonadIO m,Location loc) => TSubsts -> TcM loc m ()
addSubstsM ss = do
    updateHeadTDict $ \d -> return ((),mappend d (TDict Graph.empty Set.empty ss))
    mapM_ (dirtyVarDependencies . fst) $ Map.toList ss

addSubst :: (MonadIO m,Location loc) => loc -> VarIdentifier -> Type -> TcM loc m ()
addSubst l v t = updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert v t (tSubsts d) })

addSubstM :: (MonadIO m,Location loc) => loc -> VarName VarIdentifier Type -> Type -> TcM loc m ()
addSubstM l v t | varNameToType v == t = return ()
                | typeClass "addSubstML" (varNameToType v) == typeClass "addSubstMR" t = do
                    addSubst l (varNameId v) t
                    dirtyVarDependencies (varNameId v)
                | otherwise = genTcError (locpos l) $ text "Variable" <+> quotes (pp v) <+> text "does not match type" <+> quotes (pp t)

newTyVarId :: MonadIO m => TcM loc m TyVarId
newTyVarId = do
    liftIO $ atomicModifyIORef' globalEnv $ \g -> (g { tyVarId = succ (tyVarId g) },tyVarId g)

newDomainTyVar :: (MonadIO m,Location loc) => SVarKind -> TcM loc m SecType
newDomainTyVar k = do
    n <- uniqVarId "d"
    return $ SVar n k

newDimVar :: (MonadIO m,Location loc) => TcM loc m (SExpr VarIdentifier Type)
newDimVar = do
    n <- uniqVarId "dim"
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newTypedVar :: (MonadIO m,Location loc) => String -> Type -> TcM loc m (VarName VarIdentifier Type)
newTypedVar s t = liftM (VarName t) $ uniqVarId s

newTyVar :: (MonadIO m,Location loc) => TcM loc m Type
newTyVar = do
    n <- uniqVarId "t"
    return $ ComplexT $ CVar n

newDecVar :: (MonadIO m,Location loc) => TcM loc m DecType
newDecVar = do
    n <- uniqVarId "dec"
    return $ DVar n
    
uniqVarId :: MonadIO m => Identifier -> TcM loc m VarIdentifier
uniqVarId n = do
    i <- newTyVarId
    let v = VarIdentifier n (Just i) False 
    addFree v
    return v
    
newBaseTyVar :: (MonadIO m,Location loc) => TcM loc m BaseType
newBaseTyVar = do
    n <- uniqVarId "b"
    return $ BVar n
    
newSizeVar :: (MonadIO m,Location loc) => TcM loc m (SExpr VarIdentifier Type)
newSizeVar = do
    n <- uniqVarId "sz"
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)
    
addValue :: (MonadIO m,Location loc) => loc -> VarName VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
addValue l v (e) = updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert (varNameId v) (IdxT e) (tSubsts d) })

addValueM :: (MonadIO m,Location loc) => loc -> VarName VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
addValueM l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
addValueM l v@(VarName t n) (e) | typeClass "addValueL" t == typeClass "addValueR" (loc e) = do
    addValue l v e
    addVarDependencies n
    dirtyVarDependencies n
addValueM l v e = genTcError (locpos l) $ text "unification: mismatching expression types"

openCstr l iok = do
    opts <- TcM $ lift ask
    size <- liftM (length . openedCstrs) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "opened constraints"
        else State.modify $ \e -> e { openedCstrs = Set.insert iok $ openedCstrs e }

resolveIOCstr :: (MonadIO m,Location loc) => loc -> IOCstr -> (TCstr -> TcM loc m ShowOrdDyn) -> TcM loc m ShowOrdDyn
resolveIOCstr l iok resolve = do
    st <- liftIO $ readUniqRef (kStatus iok)
    case st of
        Evaluated x -> do
            remove
            return x
        Erroneous err -> throwError err
        Unevaluated -> trySolve
  where
    trySolve = do
        openCstr l iok
        t <- resolve $ kCstr iok
        liftIO $ writeUniqRef (kStatus iok) $ Evaluated t
        State.modify $ \e -> e { openedCstrs = Set.delete iok (openedCstrs e) } 
        -- register constraints dependencies from the dictionary into the global state
        registerIOCstrDependencies iok
        remove
        return t
    remove = updateHeadTDict $ \d -> return ((),d { tCstrs = delNode (ioCstrId iok) (tCstrs d) })

registerIOCstrDependencies :: (MonadIO m,Location loc) => IOCstr -> TcM loc m ()
registerIOCstrDependencies iok = do
    gr <- liftM (tCstrs . headNe . tDict) State.get
    case contextGr gr (ioCstrId iok) of
        Nothing -> return ()
        Just (deps,_,_,_) -> forM_ deps $ \(_,d) -> case lab gr d of
            Nothing -> return ()
            Just x -> addIODependency (unLoc x) (Set.singleton iok)

-- | adds a dependency on the given variable for all the opened constraints
addVarDependencies :: (MonadIO m,Location loc) => VarIdentifier -> TcM loc m ()
addVarDependencies v = do
    cstrs <- liftM openedCstrs State.get
    addVarDependency v cstrs
    
addVarDependency :: (MonadIO m,Location loc) => VarIdentifier -> Set IOCstr -> TcM loc m ()
addVarDependency v cstrs = do
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps v
    m <- case mb of
        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps v m (MkWeak $ mkWeakKey m) >> return m
        Just m -> return m
    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) k (MkWeak $ mkWeakKey $ kStatus k)
--    liftIO $ modifyIORef' globalEnv $ \g -> g { tDeps = Map.insertWith (Set.union) v cstrs (tDeps g) }

addIODependency :: (MonadIO m,Location loc) => IOCstr -> Set IOCstr -> TcM loc m ()
addIODependency v cstrs = do
    deps <- liftM ioDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps (uniqId $ kStatus v)
    m <- case mb of
        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps (uniqId $ kStatus v) m (MkWeak $ mkWeakKey m) >> return m
        Just m -> return m
    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) k (MkWeak $ mkWeakKey $ kStatus k)

-- adds a dependency to the constraint graph
addIOCstrDependencies :: TDict loc -> Set Int -> Loc loc IOCstr -> Set Int -> TDict loc
addIOCstrDependencies dict from iok to = dict { tCstrs = (froms,ioCstrId (unLoc iok),iok,tos) & (tCstrs dict) }
    where
    tos = map ((),) $ Set.toList to
    froms = map ((),) $ Set.toList from
    
--    deps <- liftM ioDeps $ liftIO $ readIORef globalEnv
--    let uid = uniqId $ kStatus iok
--    mb <- liftIO $ WeakHash.lookup deps uid
--    m <- case mb of
--        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps uid m (MkWeak $ mkWeakKey m) >> return m
--        Just m -> return m
--    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) k (MkWeak $ mkWeakKey $ kStatus k)

addIOCstrDependenciesM :: (Monad m,Location loc) => Set Int -> Loc loc IOCstr -> Set Int -> TcM loc m ()
addIOCstrDependenciesM froms iok tos = do
    updateHeadTDict $ \d -> return ((),addIOCstrDependencies d froms iok tos)
    
addHeadTDict :: (Monad m,Location loc) => TDict loc -> TcM loc m ()
addHeadTDict d = updateHeadTDict $ \x -> return ((),mappend x d)

getHyps :: (MonadIO m,Location loc) => TcM loc m (Hyps loc)
getHyps = do
    env <- State.get
    return $ globalHyps env `Set.union` localHyps env

tcWithCstrs :: (VarsIdTcM loc m,Location loc) => loc -> TcM loc m a -> TcM loc m (a,Set IOCstr)
tcWithCstrs l m = do
    (x,d) <- tcWith l m
    addHeadTDict d
    return (x,flattenIOCstrGraphSet $ tCstrs d)

newIOCstr :: TCstr -> TCstrStatus -> IO IOCstr
newIOCstr c res = do
    st <- newUniqRef res
    let io = IOCstr c st
    return io

cstrSetToGraph :: loc -> Set IOCstr -> IOCstrGraph loc
cstrSetToGraph l xs = foldr (\x gr -> insNode (ioCstrId x,Loc l x) gr) Graph.empty (Set.toList xs)

insertTDictCstr :: (MonadIO m,Location loc) => loc -> TCstr -> TCstrStatus -> TDict loc -> TcM loc m (IOCstr,TDict loc)
insertTDictCstr l c res dict = do
    iok <- liftIO $ newIOCstr c res
--    vs <- fvIds c
--    forM_ vs $ \v -> addVarDependency v $ Set.singleton io
    return (iok,dict { tCstrs = insNode (ioCstrId iok,Loc l iok) (tCstrs dict) })

---- | Adds a new template constraint to the environment
newTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> TcM loc m IOCstr
newTemplateConstraint l c = do
    updateHeadTDict (insertTDictCstr l c Unevaluated)

updateHeadTDict :: (Monad m,Location loc) => (TDict loc -> TcM loc m (a,TDict loc)) -> TcM loc m a
updateHeadTDict upd = do
    e <- State.get
    (x,d') <- updHeadNeM upd (tDict e)
    let e' = e { tDict = d' }
    State.put e'
    return x

-- | forget the result for a constraint when the value of a variable it depends on changes
dirtyVarDependencies :: (MonadIO m,Location loc) => VarIdentifier -> TcM loc m ()
dirtyVarDependencies v = do
    cstrs <- liftM openedCstrs State.get
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps v
    case mb of
        Nothing -> return ()
        Just m -> do
            WeakMap.forGenericM_ m $ \(u,x) -> unless (elem x cstrs) $ do
                liftIO $ writeUniqRef (kStatus x) Unevaluated
                -- dirty other constraint dependencies
                dirtyIOCstrDependencies x

dirtyIOCstrDependencies :: (MonadIO m,Location loc) => IOCstr -> TcM loc m ()
dirtyIOCstrDependencies iok = do
    deps <- liftM ioDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps (uniqId $ kStatus iok)
    case mb of
        Nothing -> return ()
        Just m -> liftIO $ WeakMap.forM_ m $ \(u,x) -> writeUniqRef (kStatus x) Unevaluated

vars env = Map.union (localVars env) (globalVars env)

tcWarn :: (Monad m,Location loc) => Position -> TypecheckerWarn -> TcM loc m ()
tcWarn pos msg = do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Set.singleton $ TypecheckerWarning pos msg

errWarn :: (Monad m,Location loc) => SecrecError -> TcM loc m ()
errWarn msg = do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Set.singleton $ ErrWarn msg

isChoice :: (Monad m,Location loc) => Unique -> TcM loc m Bool
isChoice x = liftM (Set.member (hashUnique x) . tChoices . mconcatNe . tDict) State.get

addChoice :: (Monad m,Location loc) => Unique -> TcM loc m ()
addChoice x = updateHeadTDict $ \d -> return ((),d { tChoices = Set.insert (hashUnique x) $ tChoices d })
