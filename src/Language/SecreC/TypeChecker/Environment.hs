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

import Text.PrettyPrint as PP hiding (float,int)
import qualified Text.PrettyPrint as Pretty

import qualified Data.HashTable.Weak.IO as WeakHash
import qualified System.Mem.Weak.Map as WeakMap

import System.Mem.Weak.Exts as Weak

-- | Gets the variables of a given type class
getVars :: Location loc => Scope -> TypeClass -> TcM loc (Map VarIdentifier (EntryEnv loc))
getVars GlobalScope c = do
    vs <- liftM globalVars State.get
    return $ Map.filter (\e -> typeClass "getVarsG" (entryType e) == c) vs
getVars LocalScope c = do
    vs <- liftM vars State.get
    return $ Map.filterWithKey (\k e -> typeClass ("getVarsL " ++ ppr k ++ ppr (locpos $ entryLoc e)) (entryType e) == c) vs

addVar :: Location loc => Scope -> VarIdentifier -> EntryEnv loc -> TcM loc ()
addVar GlobalScope n e = modify $ \env -> env { globalVars = Map.insert n e (globalVars env) }
addVar LocalScope n e = modify $ \env -> env { localVars = Map.insert n e (localVars env) }

checkVariable :: Location loc => Scope -> VarName VarIdentifier loc -> TcM loc Type
checkVariable scope (VarName l n) = do
    vs <- getVars scope TypeC
    case Map.lookup n vs of
        Just e -> return $ entryType e
        Nothing -> tcError (locpos l) $ VariableNotFound (ppVarId n)

-- | Adds a new variable to the environment
newVariable :: Location loc => Scope -> VarName VarIdentifier (Typed loc) -> EntryValue loc -> TcM loc ()
newVariable scope (VarName (Typed l t) n) val = do
    vars <- getVars scope TypeC
    case Map.lookup n vars of
        Just e -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
        Nothing -> return ()
    addVar scope n (EntryEnv l t val)

-- | Adds a new domain variable to the environment
newDomainVariable :: Location loc => Scope -> DomainName VarIdentifier (Typed loc) -> TcM loc ()
newDomainVariable scope (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ InvalidDomainVariableName (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            vars <- getVars scope KindC
            case Map.lookup n vars of
                Just e -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
                Nothing -> addVar scope n (EntryEnv l t UnknownValue)

-- | Adds a new type variable to the environment
newTypeVariable :: Location loc => Scope -> TypeName VarIdentifier (Typed loc) -> TcM loc ()
newTypeVariable scope (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (b,es) -> tcError (locpos l) $ InvalidTypeVariableName (ppVarId n) (map (locpos . entryLoc) (b:Map.elems es))
        Nothing -> do
            vars <- getVars scope TypeStarC
            case Map.lookup n vars of
                Just e -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
                Nothing -> addVar scope n (EntryEnv l t UnknownValue)

-- | Adds a new domain to the environment
newDomain :: Location loc => DomainName VarIdentifier (Typed loc) -> TcM loc ()
newDomain (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ MultipleDefinedDomain (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t UnknownValue
            modify $ \env -> env { domains = Map.insert n e (domains env) }

-- | Checks if a domain exists in scope, and returns its type
-- Searches for both user-defined private domains and domain variables
checkDomain :: Location loc => DomainName VarIdentifier loc -> TcM loc Type
checkDomain (DomainName l n) = do
    ds <- liftM domains State.get
    case Map.lookup n ds of
        Just e -> case entryType e of
            SType (PrivateKind (Just k)) -> return $ SecT $ Private (DomainName () n) k
            otherwise -> genericError (locpos l) $ text "Unexpected domain" <+> quotes (pp n) <+> text "without kind."
        Nothing -> do
            dvars <- getVars LocalScope KindC
            case Map.lookup n dvars of
                Just e -> return $ varNameToType $ VarName (entryType e) n
                Nothing -> tcError (locpos l) $ NotDefinedDomain (ppVarId n)

-- | Checks if a type exists in scope
-- Searches for both user-defined types and type variables
checkType :: Location loc => TypeName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkType (TypeName l n) = do
    ss <- liftM structs State.get
    case Map.lookup n ss of
        Just (base,es) -> return (base : Map.elems es)
        Nothing -> do
            vars <- getVars LocalScope TypeStarC
            case Map.lookup n vars of
                Just e -> return [ e { entryType = varNameToType (VarName (entryType e) n) } ] -- return the type variable
                Nothing -> tcError (locpos l) $ NotDefinedType (ppVarId n)

-- | Checks if a non-template type exists in scope
-- Returns a single match
checkNonTemplateType :: Location loc => TypeName VarIdentifier loc -> TcM loc Type
checkNonTemplateType tn@(TypeName l n) = do
    es <- checkType tn
    case es of
        [e] -> case entryType e of
            DecT d -> return $ BaseT $ TyDec d
            t -> return t
        es -> tcError (locpos l) $ NoNonTemplateType (ppVarId n)

-- | Checks if a template type exists in scope
-- Returns all template type declarations in scope, base template first
checkTemplateType :: Location loc => TypeName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkTemplateType ty@(TypeName _ n) = do
    es <- checkType ty
    let check e = unless (isStructTemplate $ entryType e) $ tcError (locpos $ loc ty) $ NoTemplateType (ppVarId n) (locpos $ entryLoc e) (pp $ entryType e)
    mapM_ check es
    return es

-- | Checks if a variable argument of a template exists in scope
-- The argument can be a (user-defined or variable) type, a (user-defined or variable) domain or a dimension variable
checkTemplateArg :: Location loc => TemplateArgName VarIdentifier loc -> TcM loc Type
checkTemplateArg (TemplateArgName l vn) = do
    env <- State.get
    let ss = structs env
    let ds = domains env
    let vs = vars env
    case (Map.lookup vn ss,Map.lookup vn ds,Map.lookup vn vs) of
        (Just (base,es),Nothing,Nothing) -> case (base:Map.elems es) of
            [e] -> if (isStructTemplate $ entryType e)
                then tcError (locpos l) $ NoNonTemplateType (ppVarId vn)
                else return $ entryType e
            es -> tcError (locpos l) $ NoNonTemplateType (ppVarId vn)
        (Nothing,Just e,Nothing) -> case entryType e of
            SType (PrivateKind (Just k)) -> return $ SecT $ Private (DomainName () vn) k
            otherwise -> genericError (locpos l) $ text "Unexpected domain" <+> quotes (pp vn) <+> text "without kind."
        (Nothing,Nothing,Just e) -> return $ varNameToType $ VarName (entryType e) vn
        (mb1,mb2,mb3) -> tcError (locpos l) $ AmbiguousName (ppVarId vn) $ map (locpos . entryLoc) $ maybe [] (\(b,es) -> b:Map.elems es) mb1 ++ maybeToList mb2 ++ maybeToList mb3

-- | Checks that a kind exists in scope
checkKind :: Location loc => KindName VarIdentifier loc -> TcM loc ()
checkKind (KindName l n) = do
    ks <- liftM kinds State.get
    case Map.lookup n ks of
        Just e -> return ()
        Nothing -> tcError (locpos l) $ NotDefinedKind (ppVarId n)

-- | Adds a new kind to the environment
newKind :: Location loc => KindName VarIdentifier (Typed loc) -> TcM loc ()
newKind (KindName (Typed l t) n) = do
    ks <- liftM kinds get
    case Map.lookup n ks of
        Just e -> tcError (locpos l) $ MultipleDefinedKind (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t UnknownValue
            modify $ \env -> env { kinds = Map.insert n e (kinds env) } 

-- solves all possible head constraints
solveTemplate :: (VarsTcM loc,Location loc) => loc -> TcM loc ()
solveTemplate l = do
    opts <- TcM $ lift $ Reader.ask
    if typecheckTemplates opts
        then solve l False
        else return ()

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: (VarsTcM loc,Location loc) => [VarName VarIdentifier Type] -> Op VarIdentifier (Typed loc) -> TcM loc ()
addTemplateOperator vars op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    let o = fmap (const ()) op
    solveTemplate l
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] d) UnknownValue
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (VarsTcM loc,Location loc) => Op VarIdentifier (Typed loc) -> TcM loc ()
newOperator op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    i <- case decTypeTyVarId d of
        Just i -> return i
        otherwise -> genericError (locpos l) $ text "Unresolved declaration for operator" <+> pp op
    let o = fmap (const ()) op
    let e = EntryEnv l t UnknownValue
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
  
 -- | Checks that an operator exists.
checkOperator :: (VarsTcM loc,Location loc) => Op VarIdentifier loc -> TcM loc [EntryEnv loc]
checkOperator op@(OpCast l t) = do
    ps <- liftM operators State.get
    let cop = fmap (const ()) op
    -- select all cast declarations
    let casts = concatMap Map.elems $ Map.elems $ Map.filterWithKey (\k v -> isJust $ isOpCast k) ps
    return casts
checkOperator op = do
    ps <- liftM operators State.get
    let cop = fmap (const ()) op
    case Map.lookup cop ps of
        Nothing -> tcError (locpos $ loc op) $ Halt $ NotDefinedOperator $ pp cop
        Just es -> return $ Map.elems es
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: (VarsTcM loc,Location loc) => [VarName VarIdentifier Type] -> ProcedureName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateProcedure vars (ProcedureName (Typed l t) n) = do
    dt <- typeToDecType l t
    solveTemplate l
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] dt) UnknownValue
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: (VarsTcM loc,Location loc) => ProcedureName VarIdentifier (Typed loc) -> TcM loc ()
newProcedure (ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    i <- case decTypeTyVarId d of
        Just i -> return i
        otherwise -> genericError (locpos l) $ text "Unresolved declaration for procedure" <+> quotes (pp n)
    let e = EntryEnv l t UnknownValue
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
  
 -- | Checks that a procedure exists.
checkProcedure :: Location loc => ProcedureName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkProcedure (ProcedureName l n) = do
    ps <- liftM procedures State.get
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ Halt $ NotDefinedProcedure (ppVarId n)
        Just es -> return $ Map.elems es
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (VarsTcM loc,Location loc) => [VarName VarIdentifier Type] -> TypeName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateStruct vars (TypeName (Typed l t) n) = do
    struct <- typeToDecType l t
    solveTemplate l
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] struct) UnknownValue
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate (ppVarId n) (locpos $ loc base)
        Nothing -> modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: (VarsTcM loc,Location loc) => [VarName VarIdentifier Type] -> [Type] -> TypeName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateStructSpecialization vars specials (TypeName (Typed l t) n) = do
    struct <- typeToDecType l t
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) specials struct) UnknownValue
    let mergeStructs (b1,s1) (b2,s2) = (b2,s1 `Map.union` s2)
    modify $ \env -> env { structs = Map.update (\(b,s) -> Just (b,Map.insert i e s)) n (structs env) }

-- | Defines a new struct type
newStruct :: Location loc => TypeName VarIdentifier (Typed loc) -> TcM loc ()
newStruct (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStruct (ppVarId n) (locpos $ entryLoc base)
        Nothing -> do
            let e = EntryEnv l t UnknownValue
            modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }

--extractUnsolved :: TcM loc [Loc loc TCstr]
--extractUnsolved = do
--    us <- liftM (tUnsolved . tDict) State.get
--    State.modify $ \env -> env { tDict = (tDict env) { tCstrs = Map.filter isJust (tCstrs $ tDict env) } }
--    return us

--addUnsolved :: [Loc loc TCstr] -> TcM loc ()
--addUnsolved us = State.modify $ \env -> env { tDict = (tDict env) { tCstrs = Map.unionWith (\mb1 mb2 -> maybe mb2 Just mb1) (tCstrs (tDict env)) (Map.fromList (zip us (repeat Nothing))) } }

--addDict :: Location loc => TDict loc -> TcM loc ()
--addDict d = modify $ \env -> env { tDict = mappend (tDict env) d }

addSubstsM :: Location loc => TSubsts -> TcM loc ()
addSubstsM ss = do
    updateHeadTDict $ \d -> return ((),mappend d (TDict Map.empty Set.empty ss))
    mapM_ (uncurry dirtyVarDependencies) $ Map.toList ss

---- | Adds a new template constraint to the environment
newTemplateConstraint :: Location loc => loc -> TCstr -> TcM loc IOCstr
newTemplateConstraint l c = do
    updateHeadTDict (insertTDictCstr l c Unevaluated)

addSubst :: Location loc => loc -> VarName VarIdentifier () -> Type -> TcM loc ()
addSubst l v t = updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert v t (tSubsts d) })

addSubstM :: Location loc => loc -> VarName VarIdentifier Type -> Type -> TcM loc ()
addSubstM l v t | varNameToType v == t = return ()
                | typeClass "addSubstML" (varNameToType v) == typeClass "addSubstMR" t = do
                    addSubst l (fmap (const ()) v) t
                    dirtyVarDependencies ov t
                | otherwise = genericError (locpos l) $ text "Variable" <+> quotes (pp v) <+> text "does not match type" <+> quotes (pp t)
  where ov = fmap (const ()) v

newTyVarId :: TcM loc TyVarId
newTyVarId = do
    liftIO $ atomicModifyIORef' globalEnv $ \g -> (g { tyVarId = succ (tyVarId g) },tyVarId g)

newDomainTyVar :: Location loc => SVarKind -> TcM loc SecType
newDomainTyVar k = do
    n <- uniqVarId "d"
    let v = VarName () n
    return $ SVar v k

newDimVar :: Location loc => TcM loc (Expression VarIdentifier Type)
newDimVar = do
    n <- uniqVarId "dim"
    let v = VarName (BaseT index) n
    return $ RVariablePExpr (BaseT index) v

newTyVar :: Location loc => TcM loc Type
newTyVar = do
    n <- uniqVarId "t"
    let v = VarName () n
    return $ ComplexT $ CVar v

newDecVar :: Location loc => TcM loc DecType
newDecVar = do
    n <- uniqVarId "dec"
    let v = VarName () n
    return $ DVar v
    
uniqVarId :: Identifier -> TcM loc VarIdentifier
uniqVarId n = do
    i <- newTyVarId
    return $ VarIdentifier n (Just i) False
    
newBaseTyVar :: Location loc => TcM loc BaseType
newBaseTyVar = do
    n <- uniqVarId "b"
    let v = VarName () n
    return $ BVar v
    
newSizeVar :: Location loc => TcM loc (Expression VarIdentifier Type)
newSizeVar = do
    n <- uniqVarId "sz"
    let v = VarName (BaseT index) n
    return $ RVariablePExpr (BaseT index) v
    
addValue :: Location loc => loc -> VarName VarIdentifier (Typed loc) -> Expression VarIdentifier (Typed loc) -> TcM loc ()
addValue l v e = updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert (fmap (const ()) v) (IdxT $ fmap typed e) (tSubsts d) })
    
addValueM :: Location loc => loc -> VarName VarIdentifier (Typed loc) -> Expression VarIdentifier (Typed loc) -> TcM loc ()
addValueM l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
addValueM l v@(VarName t n) e | typeClass "addValueL" (typed t) == typeClass "addValueR" (typed $ loc e) = do
    addValue l v e
    dirtyVarDependencies (VarName () n) (IdxT $ fmap typed e)
addValueM l v e = genericError (locpos l) $ text "unification: mismatching expression types"

openCstr l iok = do
    opts <- TcM $ lift ask
    size <- liftM (length . openedCstrs) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded (constraintStackSize opts)
        else State.modify $ \e -> e { openedCstrs = Set.insert iok $ openedCstrs e }

newDict l = do
    opts <- TcM $ lift ask
    size <- liftM (lengthNe . tDict) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded (constraintStackSize opts)
        else State.modify $ \e -> e { tDict = ConsNe mempty (tDict e) }

resolveIOCstr :: Location loc => loc -> IOCstr -> (loc -> TCstr -> TcM loc ()) -> TcM loc ()
resolveIOCstr l iok resolve = do
    st <- liftIO $ readUniqRef (kStatus iok)
    case st of
        Evaluated -> remove
        Erroneous err -> throwError err
        Unevaluated -> trySolve
  where
    trySolve = do
        openCstr l iok
        t <- resolve l $ kCstr iok
        liftIO $ writeUniqRef (kStatus iok) Evaluated
        State.modify $ \e -> e { openedCstrs = Set.delete iok (openedCstrs e) } 
        remove
        return t
    remove = updateHeadTDict $ \d -> return ((),d { tCstrs = Map.delete (uniqId $ kStatus iok) (tCstrs d) })

-- | adds a dependency on the given variable for all the opened constraints
addVarDependencies :: Location loc => VarName VarIdentifier () -> TcM loc ()
addVarDependencies v = do
    cstrs <- liftM openedCstrs State.get
    addVarDependency v cstrs
    
addVarDependency :: Location loc => VarName VarIdentifier () -> Set IOCstr -> TcM loc ()
addVarDependency v cstrs = do
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps (varNameId v)
    m <- case mb of
        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps (varNameId v) m (MkWeak $ mkWeakKey m) >> return m
        Just m -> return m
    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) (kStatus k) (MkWeak $ mkWeakKey $ kStatus k)
    
--    liftIO $ modifyIORef' globalEnv $ \g -> g { tDeps = Map.insertWith (Set.union) v cstrs (tDeps g) }

addHeadTDict :: Location loc => TDict loc -> TcM loc ()
addHeadTDict d = updateHeadTDict $ \x -> return ((),mappend x d)

updateHeadTDict :: Location loc => (TDict loc -> TcM loc (a,TDict loc)) -> TcM loc a
updateHeadTDict upd = do
    e <- State.get
    (x,d') <- updHeadNeM upd (tDict e)
    let e' = e { tDict = d' }
    State.put e'
    return x

-- | forget the result for a constraint when the value of a variable it depends on changes
dirtyVarDependencies :: Location loc => VarName VarIdentifier () -> Type -> TcM loc ()
dirtyVarDependencies v t = do
    cstrs <- liftM openedCstrs State.get
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
--    liftIO $ putStrLn $ "dirtyDependencies " ++ ppr v ++ " " ++ ppr t
    mb <- liftIO $ WeakHash.lookup deps (varNameId v)
    case mb of
        Nothing -> return ()
        Just m -> do
            liftIO $ WeakMap.forM_ m $ \(u,x) -> unless (elem x $ Set.map kStatus cstrs) $ writeUniqRef x Unevaluated

--    case Map.lookup v deps of
--        Nothing -> return ()
--        Just ios -> do
----            liftIO $ putStrLn $ "deps " ++ show (map (show . hashUnique . uniqId . kStatus) $ Set.toList ios)
----            liftIO $ putStrLn $ "opens " ++ show (map (show . hashUnique . uniqId . kStatus) cstrs)
--            let dirty x = unless (elem x cstrs) $ do
----                liftIO $ putStrLn $ "dirty " ++ show (hashUnique $ uniqId $ kStatus x) ++ " " ++ ppr (kCstr x)
--                liftIO $ writeUniqRef (kStatus x) Unevaluated
--            mapM_ dirty ios

fvIds :: Vars m a => a -> m (Set VarIdentifier)
fvIds = liftM scVarsIds . fvs

scVarsIds :: Set ScVar -> Set VarIdentifier
scVarsIds = Set.unions . map scVarIds . Set.toList

scVarIds :: ScVar -> Set VarIdentifier
scVarIds (ScVar a) = everything (Set.union) (mkQ Set.empty f) a
    where
    f :: VarIdentifier -> Set VarIdentifier
    f = Set.singleton

vars env = Map.union (localVars env) (globalVars env)

filterTSubsts :: Location loc => Set VarIdentifier -> TSubsts -> TcM loc TSubsts
filterTSubsts vs ss = 
    return $ Map.filterWithKey (\k v -> varNameId k `Set.member` vs) ss
--    (g,(_,nodes)) <- graphTSubsts ss
--    let g' = trc g
--    let is = Map.elems $ Map.filterWithKey (\k v -> k `Set.member` vs) nodes
--    let os = concatMap (map snd3 . out g') is
--    let xs = Set.fromList $ map (\o -> fromJust $ lab g' o) os
--    let ios = Set.union vs xs
--    return $ Map.filterWithKey (\k v -> varNameId k `Set.member` ios) ss
--
--graphTSubsts :: TSubsts -> TcM loc (Gr VarIdentifier (),(Node,Map VarIdentifier Node))
--graphTSubsts ss = runStateT (graphTSubsts' ss) (0,Map.empty)
--    where
--    graphTSubsts' :: TSubsts -> StateT (Node,Map VarIdentifier Node) (TcM loc) (Gr VarIdentifier ())    
--    graphTSubsts' ss = Map.foldrWithKey addG (return Graph.empty) ss
--        where
--        addG v t mg = do
--            g <- mg
--            i <- newNode $ varNameId v
--            os <- mapM newNode =<< liftM Set.toList (fvIds t)
--            return $ ([],i,varNameId v,map ((),) os) & g
--        newNode v = do
--            (i,xs) <- State.get
--            case Map.lookup v xs of
--                Just j -> return j
--                Nothing -> do
--                    State.put (succ i,Map.insert v i xs)
--                    return i

getTSubsts :: Location loc => TcM loc TSubsts
getTSubsts = do
    env <- State.get
    let es = Map.foldrWithKey (\k e m -> case entryValue e of { KnownExpression ex -> Map.insert (VarName () k) (IdxT $ fmap typed ex) m; otherwise -> m}) Map.empty $ vars env
    let sst = tSubsts $ mconcatNe $ tDict env
    return $ Map.unions [es,sst]
    
tcError :: Location loc => Position -> TypecheckerErr -> TcM loc a
tcError pos msg = do
    f <- Reader.ask
    let err = f $ typecheckerError pos msg
    ios <- liftM openedCstrs State.get
    let add io = liftIO $ writeUniqRef (kStatus io) (Erroneous err)
    mapM_ add ios
    throwError err

tcWarn :: Location loc => Position -> TypecheckerWarn -> TcM loc ()
tcWarn pos msg = TcM $ lift $ tell [TypecheckerWarning pos msg]

isChoice :: Location loc => Unique -> TcM loc Bool
isChoice x = liftM (Set.member x . tChoices . mconcatNe . tDict) State.get

addChoice :: Location loc => Unique -> TcM loc ()
addChoice x = updateHeadTDict $ \d -> return ((),d { tChoices = Set.insert x $ tChoices d })
