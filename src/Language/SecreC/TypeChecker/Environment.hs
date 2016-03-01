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
import Data.Either
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

getVars scope cl = getVarsPred scope (== cl)

-- | Gets the variables of a given type class
getVarsPred :: (MonadIO m,Location loc) => Scope -> (TypeClass -> Bool) -> TcM loc m (Map VarIdentifier (Bool,EntryEnv loc))
getVarsPred GlobalScope f = do
    vs <- liftM globalVars State.get
    return $ Map.filter (\(_,e) -> f $ typeClass "getVarsG" (entryType e)) vs
getVarsPred LocalScope f = do
    vs <- liftM vars State.get
    return $ Map.filterWithKey (\k (_,e) -> f $ typeClass ("getVarsL " ++ ppr k ++ ppr (locpos $ entryLoc e)) (entryType e)) vs

addVar :: (MonadIO m,Location loc) => Scope -> VarIdentifier -> Bool -> EntryEnv loc -> TcM loc m ()
addVar GlobalScope n b e = modify $ \env -> env { globalVars = Map.insert n (b,e) (globalVars env) }
addVar LocalScope n b e = modify $ \env -> env { localVars = Map.insert n (b,e) (localVars env) }



getFrees :: (Monad m,Location loc) => TcM loc m (Set VarIdentifier)
getFrees = liftM localFrees State.get

-- replaces a constraint in the constraint graph by a constraint graph
replaceCstrWithGraph :: (MonadIO m,Location loc) => loc -> Int -> Set (Loc loc IOCstr) -> IOCstrGraph loc -> Set (Loc loc IOCstr) -> TcM loc m ()
replaceCstrWithGraph l kid ins gr outs = do
    let cs = flattenIOCstrGraph gr
--    liftIO $ putStrLn $ "replaceCstrWithGraph " ++ ppr kid ++ " for " ++ show (sepBy space $ map (pp . ioCstrId . unLoc) cs)
    updateHeadTDict $ \d -> return ((),d { tCstrs = unionGr gr $ delNode kid (tCstrs d) })
    forM_ cs $ \c -> addIOCstrDependenciesM (Set.filter (\x -> ioCstrId (unLoc x) /= kid) ins) c (Set.filter (\x -> ioCstrId (unLoc x) /= kid) outs)
--    ss <- ppConstraints =<< liftM (headNe . tDict) State.get
--    liftIO $ putStrLn $ "replaceCstrWithGraph2 [" ++ show ss ++ "\n]"

withDeps :: MonadIO m => Scope -> TcM loc m a -> TcM loc m a
withDeps LocalScope m = do
    env <- State.get
    let l = localDeps env
    x <- m
    State.modify $ \env -> env { localDeps = l }
    return x
withDeps GlobalScope m = do
    env <- State.get
    let l = localDeps env
    let g = globalDeps env
    x <- m
    State.modify $ \env -> env { localDeps = l, globalDeps = g }
    return x

getConsts :: Monad m => TcM loc m (Map Identifier VarIdentifier)
getConsts = do
    env <- State.get
    return $ localConsts env `Map.union` globalConsts env

checkVariable :: (MonadIO m,Location loc) => Bool -> Scope -> VarName VarIdentifier loc -> TcM loc m (VarName VarIdentifier (Typed loc))
checkVariable isConst scope (VarName l n) = do
    vs <- getVarsPred scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    consts <- getConsts
    let n' = case varIdUniq n of
                Nothing -> maybe n id (Map.lookup (varIdBase n) consts)
                otherwise -> n
    case Map.lookup n' vs of
        Just (b,e) -> do
            when (isConst && b) $ tcError (locpos l) $ AssignConstVariable (pp n')
            return $ VarName (Typed l $ entryType e) n'
        Nothing -> tcError (locpos l) $ VariableNotFound (pp n')

-- | Adds a new variable to the environment
newVariable :: (MonadIO m,VarsIdTcM loc m,Location loc) => Scope -> VarName VarIdentifier (Typed loc) -> Maybe (Expression VarIdentifier (Typed loc)) -> Bool -> TcM loc m ()
newVariable scope v@(VarName (Typed l t) n) val isConst = do
    vars <- getVarsPred scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    case Map.lookup n vars of
        Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (ppVarId n) (locpos $ entryLoc e)
        Nothing -> return ()
    addVar scope n isConst (EntryEnv l t)
--    case scope of
--        LocalScope -> addFree n
--        otherwise -> return ()
    case val of
        Just e -> do
            unifiesExprTy l (fmap typed $ varExpr v) (fmap typed e)
        Nothing -> return ()

addDeps :: (MonadIO m,Location loc) => Scope -> Set (Loc loc IOCstr) -> TcM loc m ()
addDeps scope xs = forM_ xs $ \x -> addDep scope x

addDep :: (MonadIO m,Location loc) => Scope -> Loc loc IOCstr -> TcM loc m ()
addDep GlobalScope hyp = modify $ \env -> env { globalDeps = Set.insert hyp (globalDeps env) }
addDep LocalScope hyp = modify $ \env -> env { localDeps = Set.insert hyp (localDeps env) }

tcNoDeps :: (VarsIdTcM loc m,Location loc) => TcM loc m a -> TcM loc m a
tcNoDeps m = do
    env <- State.get
    let g = globalDeps env
    let l = localDeps env
    State.modify $ \env -> env { globalDeps = Set.empty, localDeps = Set.empty }
    x <- m
    State.modify $ \env -> env { globalDeps = g, localDeps = l }
    return x

tcAddDeps :: (VarsIdTcM loc m,Location loc) => loc -> String -> TcM loc m a -> TcM loc m a
tcAddDeps l msg m = do
    (x,ks) <- tcWithCstrs l msg m
    forM_ ks $ addDep LocalScope
    return x
    
tryAddHypothesis :: (MonadIO m,Location loc) => loc -> Scope -> Set (Loc loc IOCstr) -> HypCstr -> TcM loc m ()
tryAddHypothesis l scope deps hyp = do
    iok <- updateHeadTDict $ \d -> insertTDictCstr l (HypK hyp) Unevaluated d
    addDep scope $ Loc l iok
    addIOCstrDependenciesM deps (Loc l iok) Set.empty

-- | Adds a new domain variable to the environment
newDomainVariable :: (MonadIO m,Location loc) => Scope -> DomainName VarIdentifier (Typed loc) -> TcM loc m ()
newDomainVariable scope (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ InvalidDomainVariableName (ppVarId n) (locpos $ entryLoc e)
        Nothing -> do
            vars <- getVarsPred scope (\k -> k == KindC || k == VArrayC KindC)
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
            vars <- getVarsPred scope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
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

isDomain k = k == KindC || k == VArrayC KindC

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
            dvars <- getVarsPred LocalScope isDomain
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
            vars <- getVarsPred LocalScope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
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
addTemplateOperator :: (VarsIdTcM loc m,Location loc) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps loc -> Op VarIdentifier (Typed loc) -> TcM loc m (Op VarIdentifier (Typed loc))
addTemplateOperator vars hdeps op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    let o = funit op
    solve l
    (hdict,bdict) <- splitHeadTDict hdeps
    i <- newTyVarId
    frees <- getFrees
    let td = DecT $ TpltType i vars (fmap locpos hdict) (fmap locpos bdict) [] frees d
    let e = EntryEnv l td
--    liftIO $ putStrLn $ "addTemplateOp " ++ ppr (entryType e)
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) td)

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (VarsIdTcM loc m,Location loc) => Op VarIdentifier (Typed loc) -> TcM loc m (Op VarIdentifier (Typed loc))
newOperator op = do
    let Typed l t = loc op
    solve l
    frees <- getFrees
    d <- typeToDecType l t
    i <- newTyVarId
    let o = funit op
    dict <- liftM (headNe . tDict) State.get
    let td = DecT $ TpltType i [] (fmap locpos dict) mempty [] frees d
    let e = EntryEnv l td
    liftIO $ putStrLn $ "addOp " ++ ppr (entryType e)
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) td)
  
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
addTemplateProcedure :: (VarsIdTcM loc m,Location loc) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps loc -> ProcedureName VarIdentifier (Typed loc) -> TcM loc m (ProcedureName VarIdentifier (Typed loc))
addTemplateProcedure vars hdeps pn@(ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    (hdict,bdict) <- splitHeadTDict hdeps
    i <- newTyVarId
    frees <- getFrees
    let dt = DecT $ TpltType i vars (fmap locpos hdict) (fmap locpos bdict) [] frees d
    let e = EntryEnv l dt
    liftIO $ putStrLn $ "addTemplateProc " ++ ppr (entryType e)
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ updLoc pn (Typed (unTyped $ loc pn) dt)

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: (VarsIdTcM loc m,Location loc) => ProcedureName VarIdentifier (Typed loc) -> TcM loc m (ProcedureName VarIdentifier (Typed loc))
newProcedure pn@(ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    frees <- getFrees
    i <- newTyVarId
    dict <- liftM (headNe . tDict) State.get
    let dt = DecT $ TpltType i [] (fmap locpos dict) mempty [] frees d
    let e = EntryEnv l dt
    liftIO $ putStrLn $ "addProc " ++ ppr (entryType e)
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ updLoc pn (Typed (unTyped $ loc pn) dt)
  
 -- | Checks that a procedure exists.
checkProcedure :: (MonadIO m,Location loc) => ProcedureName VarIdentifier loc -> TcM loc m [EntryEnv loc]
checkProcedure (ProcedureName l n) = do
    ps <- liftM procedures State.get
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ Halt $ NotDefinedProcedure (ppVarId n)
        Just es -> return $ Map.elems es
    
buildCstrGraph :: MonadIO m => Set (Loc loc IOCstr) -> TcM loc m (IOCstrGraph loc)
buildCstrGraph cstrs = do
    gr <- liftM (tCstrs . mconcatNe . tDict) State.get
    let tgr = Graph.trc gr 
    opens <- liftM openedCstrs State.get
    let cs = Set.difference (mapSet unLoc cstrs) (Set.fromList opens)
    let gr' = Graph.nfilter (\n -> any (\h -> Graph.hasEdge tgr (n,ioCstrId h)) cs) tgr
    return gr'
    
splitHeadTDict :: Monad m => Set (Loc loc IOCstr) -> TcM loc m (TDict loc,TDict loc)
splitHeadTDict deps = do
    d <- liftM (headNe . tDict) State.get
    opens <- liftM openedCstrs State.get
    let cs = Set.difference (mapSet unLoc deps) (Set.fromList opens)
    let gr = Graph.trc $ tCstrs d
    let hgr = Graph.nfilter (\n -> any (\h -> Graph.hasEdge gr (n,ioCstrId h)) cs) gr
    let bgr = Graph.nfilter (\n -> not $ any (\h -> Graph.hasEdge gr (n,ioCstrId h)) cs) gr
    return (TDict hgr (tChoices d) (tSubsts d),TDict bgr Set.empty Map.empty)
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (VarsIdTcM loc m,Location loc) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps loc -> TypeName VarIdentifier (Typed loc) -> TcM loc m (TypeName VarIdentifier (Typed loc))
addTemplateStruct vars hdeps tn@(TypeName (Typed l t) n) = do
    struct <- typeToDecType l t
    solve l
    (hdict,bdict) <- splitHeadTDict hdeps
    i <- newTyVarId
    frees <- getFrees
    let dt = DecT $ TpltType i vars (fmap locpos hdict) (fmap locpos bdict) [] frees struct
    let e = EntryEnv l dt
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate (ppVarId n) (locpos $ loc base)
        Nothing -> modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
    return $ updLoc tn (Typed (unTyped $ loc tn) dt)
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: (VarsIdTcM loc m,Location loc) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> [(Type,IsVariadic)] -> Deps loc -> TypeName VarIdentifier (Typed loc) -> TcM loc m (TypeName VarIdentifier (Typed loc))
addTemplateStructSpecialization vars specials hdeps tn@(TypeName (Typed l t) n) = do
    struct <- typeToDecType l t
    solve l
    (hdict,bdict) <- splitHeadTDict hdeps
    i <- newTyVarId
    frees <- getFrees
    let dt = DecT $ TpltType i vars (fmap locpos hdict) (fmap locpos bdict) specials frees struct
    let e = EntryEnv l dt
    let mergeStructs (b1,s1) (b2,s2) = (b2,s1 `Map.union` s2)
    modify $ \env -> env { structs = Map.update (\(b,s) -> Just (b,Map.insert i e s)) n (structs env) }
    return $ updLoc tn (Typed (unTyped $ loc tn) dt)

-- | Defines a new struct type
newStruct :: (VarsIdTcM loc m,Location loc) => TypeName VarIdentifier (Typed loc) -> TcM loc m (TypeName VarIdentifier (Typed loc))
newStruct tn@(TypeName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    frees <- getFrees
    dict <- liftM (headNe . tDict) State.get
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStruct (ppVarId n) (locpos $ entryLoc base)
        Nothing -> do
            i <- newTyVarId
            let dt = DecT $ TpltType i [] (fmap locpos dict) mempty [] frees d
            let e = EntryEnv l dt
            modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
            return $ updLoc tn (Typed (unTyped $ loc tn) dt)

addSubst :: (MonadIO m,Location loc) => loc -> VarIdentifier -> Type -> TcM loc m ()
addSubst l v t = do
--    liftIO $ putStrLn $ "addSubst " ++ ppr v ++ " = " ++ ppr t
    updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert v t (tSubsts d) })

addSubsts :: (MonadIO m,Location loc) => TSubsts -> TcM loc m ()
addSubsts ss = do
--    liftIO $ putStrLn $ "addSubstsM " ++ ppr ss
    updateHeadTDict $ \d -> return ((),mappend d (TDict Graph.empty Set.empty ss))
    mapM_ (dirtyVarDependencies . fst) $ Map.toList ss

addSubstM :: (VarsIdTcM loc m,Location loc) => loc -> VarName VarIdentifier Type -> Type -> TcM loc m ()
addSubstM l v t | varNameToType v == t = return ()
addSubstM l v t = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
    tcCstrM l $ Unifies (loc v) (tyOf t)
    addSubst l (varNameId v) t
    dirtyVarDependencies (varNameId v)
    
--addSubstM l v t | varNameToType v == t = return ()
--                | typeClass "addSubstML" (varNameToType v) == typeClass "addSubstMR" t = do
--                    addSubst l (varNameId v) t
--                    dirtyVarDependencies (varNameId v)
--                | otherwise = genTcError (locpos l) $ text "Variable" <+> quotes (pp v) <+> text "does not match type" <+> quotes (pp t)

newDomainTyVar :: (MonadIO m,Location loc) => SVarKind -> TcM loc m SecType
newDomainTyVar k = do
    n <- uniqVarId "d"
    return $ SVar n k

newDimVar :: (MonadIO m,Location loc) => TcM loc m (SExpr VarIdentifier Type)
newDimVar = do
    n <- uniqVarId "dim"
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newTypedVar :: (MonadIO m,Location loc) => String -> a -> TcM loc m (VarName VarIdentifier a)
newTypedVar s t = liftM (VarName t) $ uniqVarId s

newVarOf :: (MonadIO m,Location loc) => String -> Type -> TcM loc m Type
newVarOf str TType = newTyVar
newVarOf str BType = liftM BaseT $ newBaseTyVar
newVarOf str (SType k) = liftM SecT $ newDomainTyVar k
newVarOf str t | typeClass "newVarOf" t == TypeC = liftM (IdxT . varExpr) $ newTypedVar str t
newVarOf str (VAType b sz) = liftM VArrayT $ newArrayVar b sz

newArrayVar :: (MonadIO m,Location loc) => Type -> SExpr VarIdentifier Type -> TcM loc m VArrayType
newArrayVar b sz = do
    n <- uniqVarId "varr"
    return $ VAVar n b sz

newTyVar :: (MonadIO m,Location loc) => TcM loc m Type
newTyVar = do
    n <- uniqVarId "t"
    return $ ComplexT $ CVar n

newDecVar :: (MonadIO m,Location loc) => TcM loc m DecType
newDecVar = do
    n <- uniqVarId "dec"
    return $ DVar n
    
newBaseTyVar :: (MonadIO m,Location loc) => TcM loc m BaseType
newBaseTyVar = do
    n <- uniqVarId "b"
    return $ BVar n

newIdxVar :: (MonadIO m,Location loc) => TcM loc m (VarName VarIdentifier Type)
newIdxVar = do
    n <- uniqVarId "idx"
    let v = VarName (BaseT index) n
    return v
    
newSizeVar :: (MonadIO m,Location loc) => TcM loc m (SExpr VarIdentifier Type)
newSizeVar = do
    n <- uniqVarId "sz"
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newSizesVar :: (MonadIO m,Location loc) => SExpr VarIdentifier Type -> TcM loc m [(SExpr VarIdentifier Type,IsVariadic)]
newSizesVar dim = do
    n <- uniqVarId "szs"
    let t = VAType (BaseT index) dim
    let v = VarName t n
    return [(RVariablePExpr t v,True)]
    
mkVariadicTyArray :: (MonadIO m,Location loc) => IsVariadic -> Type -> TcM loc m Type
mkVariadicTyArray False t = return t
mkVariadicTyArray True t = do
    sz <- newSizeVar
    return $ VAType t sz
    
addValue :: (MonadIO m,Location loc) => loc -> VarIdentifier -> SExpr VarIdentifier Type -> TcM loc m ()
addValue l v e = do
--    liftIO $ putStrLn $ "addValue " ++ ppr v ++ " " ++ ppr e
    updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert v (IdxT e) (tSubsts d) })

addValueM :: (VarsIdTcM loc m,Location loc) => loc -> VarName VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
addValueM l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
addValueM l v@(VarName t n) e = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
    tcCstrM l $ Unifies t (loc e)
    addValue l n e
    addVarDependencies n
    dirtyVarDependencies n

openCstr :: (MonadIO m,Location loc) => loc -> IOCstr -> TcM loc m ()
openCstr l o = do
    opts <- TcM $ lift ask
    size <- liftM (length . openedCstrs) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded $ pp (constraintStackSize opts) <+> text "opened constraints"
        else State.modify $ \e -> e { openedCstrs = o : openedCstrs e }

closeCstr :: (MonadIO m,Location loc) => TcM loc m ()
closeCstr = do
    State.modify $ \e -> e { openedCstrs = tail (openedCstrs e) }

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
        closeCstr
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
    
addVarDependency :: (MonadIO m,Location loc) => VarIdentifier -> [IOCstr] -> TcM loc m ()
addVarDependency v cstrs = do
    deps <- liftM tDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps v
    m <- case mb of
        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps v m (MkWeak $ mkWeakKey m) >> return m
        Just m -> return m
    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) k (MkWeak $ mkWeakKey $ kStatus k)

addIODependency :: (MonadIO m,Location loc) => IOCstr -> Set IOCstr -> TcM loc m ()
addIODependency v cstrs = do
    deps <- liftM ioDeps $ liftIO $ readIORef globalEnv
    mb <- liftIO $ WeakHash.lookup deps (uniqId $ kStatus v)
    m <- case mb of
        Nothing -> liftIO $ WeakMap.new >>= \m -> WeakHash.insertWithMkWeak deps (uniqId $ kStatus v) m (MkWeak $ mkWeakKey m) >> return m
        Just m -> return m
    liftIO $ forM_ cstrs $ \k -> WeakMap.insertWithMkWeak m (uniqId $ kStatus k) k (MkWeak $ mkWeakKey $ kStatus k)

-- adds a dependency to the constraint graph
addIOCstrDependencies :: TDict loc -> Set (Loc loc IOCstr) -> Loc loc IOCstr -> Set (Loc loc IOCstr) -> TDict loc
addIOCstrDependencies dict from iok to = dict { tCstrs = insLabEdges tos $ insLabEdges froms (tCstrs dict) }
    where
    tos = map (\k -> ((gid iok,iok),(gid k,k),())) $ Set.toList to
    froms = map (\k -> ((gid k,k),(gid iok,iok),())) $ Set.toList from
    gid = ioCstrId . unLoc

addIOCstrDependenciesM :: (MonadIO m,Location loc) => Set (Loc loc IOCstr) -> Loc loc IOCstr -> Set (Loc loc IOCstr) -> TcM loc m ()
addIOCstrDependenciesM froms iok tos = do
--    liftIO $ putStrLn $ "addIOCstrDependenciesM " ++ ppr (mapSet (ioCstrId . unLoc) froms) ++ " --> " ++ ppr (ioCstrId $ unLoc iok) ++ " --> " ++ ppr (mapSet (ioCstrId . unLoc) tos)
    updateHeadTDict $ \d -> return ((),addIOCstrDependencies d froms iok tos)
    
addHeadTDict :: (Monad m,Location loc) => TDict loc -> TcM loc m ()
addHeadTDict d = updateHeadTDict $ \x -> return ((),mappend x d)

getHyps :: (MonadIO m,Location loc) => TcM loc m (Deps loc)
getHyps = do
    deps <- getDeps
    return $ Set.filter (isHypCstr . kCstr . unLoc) deps

getDeps :: (MonadIO m,Location loc) => TcM loc m (Deps loc)
getDeps = do
    env <- State.get
    return $ globalDeps env `Set.union` localDeps env

tcWithCstrs :: (VarsIdTcM loc m,Location loc) => loc -> String -> TcM loc m a -> TcM loc m (a,Set (Loc loc IOCstr))
tcWithCstrs l msg m = do
    (x,d) <- tcWith l msg m
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
    return (iok,dict { tCstrs = insNode (ioCstrId iok,Loc l iok) (tCstrs dict) })

---- | Adds a new template constraint to the environment
newTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> TcM loc m IOCstr
newTemplateConstraint l c = do
    updateHeadTDict (insertTDictCstr l c Unevaluated)

erroneousTemplateConstraint :: (MonadIO m,Location loc) => loc -> TCstr -> SecrecError -> TcM loc m IOCstr
erroneousTemplateConstraint l c err = do
    updateHeadTDict (insertTDictCstr l c $ Erroneous err)

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

-- we need global const variables to distinguish them during typechecking
addConst :: MonadIO m => Scope -> Identifier -> TcM loc m VarIdentifier
addConst scope vi = do
    vi' <- uniqVarId vi
    case scope of
        LocalScope -> State.modify $ \env -> env { localConsts = Map.insert vi vi' $ localConsts env }
        GlobalScope -> State.modify $ \env -> env { globalConsts = Map.insert vi vi' $ globalConsts env }
    return vi'

vars env = Map.union (localVars env) (globalVars env)

tcWarn :: (Monad m,Location loc) => Position -> TypecheckerWarn -> TcM loc m ()
tcWarn pos msg = do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Map.singleton pos $ Set.singleton $ TypecheckerWarning pos msg

errWarn :: (Monad m,Location loc) => SecrecError -> TcM loc m ()
errWarn msg = do
    i <- getModuleCount
    TcM $ lift $ tell $ ScWarns $ Map.singleton i $ Map.singleton (loc msg) $ Set.singleton $ ErrWarn msg

isChoice :: (Monad m,Location loc) => Unique -> TcM loc m Bool
isChoice x = liftM (Set.member (hashUnique x) . tChoices . mconcatNe . tDict) State.get

addChoice :: (Monad m,Location loc) => Unique -> TcM loc m ()
addChoice x = updateHeadTDict $ \d -> return ((),d { tChoices = Set.insert (hashUnique x) $ tChoices d })

bytes :: (MonadIO m,Location loc) => TcM loc m ComplexType
bytes = do
    sz <- newSizeVar
    return $ CType Public (TyPrim $ DatatypeUint8 ()) (indexSExpr 1) [(sz,False)]


