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
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint
import Language.SecreC.Prover.Base
import Language.SecreC.TypeChecker.Conversion

import Data.IORef
import Data.Either
import Data.Int
import Data.Word
import Data.Unique
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Generics hiding (GT,typeRep)
import Data.Dynamic hiding (typeRep)
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..),(!))
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

getAllVars scope = getVarsPred scope (const True)
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
newVariable :: (MonadIO m,ProverK loc m) => Scope -> VarName VarIdentifier (Typed loc) -> Maybe (Expression VarIdentifier (Typed loc)) -> Bool -> TcM loc m ()
newVariable scope v@(VarName (Typed l t) n) val isConst = do
    vars <- getVarsPred scope (\k -> k == TypeC || k == VArrayStarC TypeC)
    case Map.lookup n vars of
        Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
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
        Just e -> tcError (locpos l) $ InvalidDomainVariableName (pp n) (locpos $ entryLoc e)
        Nothing -> do
            vars <- getVarsPred scope (\k -> k == KindC || k == VArrayC KindC)
            case Map.lookup n vars of
                Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
                Nothing -> addVar scope n False (EntryEnv l t)

-- | Adds a new type variable to the environment
newTypeVariable :: (MonadIO m,Location loc) => Scope -> TypeName VarIdentifier (Typed loc) -> TcM loc m ()
newTypeVariable scope (TypeName (Typed l t) n) = do
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (b,es) -> tcError (locpos l) $ InvalidTypeVariableName (pp n) (map (locpos . entryLoc) (b:Map.elems es))
        Nothing -> do
            vars <- getVarsPred scope (\k -> k == TypeStarC || k == VArrayC TypeStarC)
            case Map.lookup n vars of
                Just (_,e) -> tcWarn (locpos l) $ ShadowedVariable (pp n) (locpos $ entryLoc e)
                Nothing -> addVar scope n False (EntryEnv l t)

-- | Adds a new domain to the environment
newDomain :: (MonadIO m,Location loc) => DomainName VarIdentifier (Typed loc) -> TcM loc m ()
newDomain (DomainName (Typed l t) n) = do
    ds <- liftM domains get
    case Map.lookup n ds of
        Just e -> tcError (locpos l) $ MultipleDefinedDomain (pp n) (locpos $ entryLoc e)
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
                Nothing -> tcError (locpos l) $ NotDefinedDomain (pp n)

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
            DecT d -> return $ BaseT $ TApp (funit tn) [] d
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
        Nothing -> tcError (locpos l) $ NotDefinedKind (pp n)

-- | Adds a new kind to the environment
newKind :: (MonadIO m,Location loc) => KindName VarIdentifier (Typed loc) -> TcM loc m ()
newKind (KindName (Typed l t) n) = do
    ks <- liftM kinds get
    case Map.lookup n ks of
        Just e -> tcError (locpos l) $ MultipleDefinedKind (pp n) (locpos $ entryLoc e)
        Nothing -> do
            let e = EntryEnv l t
            modify $ \env -> env { kinds = Map.insert n e (kinds env) } 

noTSubsts d = fmap locpos (d { tSubsts = Map.empty })

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps loc -> Op VarIdentifier (Typed loc) -> TcM loc m (Op VarIdentifier (Typed loc))
addTemplateOperator vars hdeps op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    let o = funit op
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    dt' <- substFromTSubsts "templateOp" l (tSubsts hdict `Map.union` tSubsts bdict) False Map.empty dt
    let e = EntryEnv l dt'
--    liftIO $ putStrLn $ "addTemplateOp " ++ ppr (entryType e)
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) dt')

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (ProverK loc m) => Deps loc -> Op VarIdentifier (Typed loc) -> TcM loc m (Op VarIdentifier (Typed loc))
newOperator hdeps op = do
    let Typed l t = loc op
    let o = funit op
    d <- typeToDecType l t
    (_,recdict) <- tcProve l "newOp head" $ addHeadTCstrs hdeps
    addHeadTDict recdict
    i <- newTyVarId
    frees <- getFrees
    d' <- substFromTDict "newOp head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] mempty Set.empty mempty frees [] d'
    let rece = EntryEnv l recdt
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i rece . maybe Map.empty id) o (operators env) }
    dirtyGDependencies $ Right $ Left $ Right o
    
    solve l
    dict <- liftM (head . tDict) State.get
    d'' <- substFromTDict "newOp body" l dict False Map.empty d'
    let td = DecT $ DecType i False [] mempty Set.empty mempty Set.empty [] d''
    let e = EntryEnv l td
--    liftIO $ putStrLn $ "addOp " ++ ppr (entryType e)
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }
    return $ updLoc op (Typed (unTyped $ loc op) td)
  
 -- | Checks that an operator exists.
checkOperator :: (VarsIdTcM loc m,Location loc) => Op VarIdentifier loc -> TcM loc m [EntryEnv loc]
checkOperator op@(OpCast l t) = do
    addGDependencies $ Right $ Left $ Right $ funit op
    ps <- liftM operators State.get
    let cop = funit op
    -- select all cast declarations
    let casts = concatMap Map.elems $ Map.elems $ Map.filterWithKey (\k v -> isJust $ isOpCast k) ps
    return casts
checkOperator op = do
    addGDependencies $ Right $ Left $ Right $ funit op
    ps <- liftM operators State.get
    let cop = funit op
    case Map.lookup cop ps of
        Nothing -> tcError (locpos $ loc op) $ Halt $ NotDefinedOperator $ pp cop
        Just es -> return $ Map.elems es
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps loc -> ProcedureName VarIdentifier (Typed loc) -> TcM loc m (ProcedureName VarIdentifier (Typed loc))
addTemplateProcedure vars hdeps pn@(ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    dt' <- substFromTSubsts "templateProc" l (tSubsts hdict `Map.union` tSubsts bdict) False Map.empty dt
    let e = EntryEnv l dt'
--    liftIO $ putStrLn $ "addTemplateProc " ++ ppr (entryType e)
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ updLoc pn (Typed (unTyped $ loc pn) dt')

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: (ProverK loc m) => Deps loc -> ProcedureName VarIdentifier (Typed loc) -> TcM loc m (ProcedureName VarIdentifier (Typed loc))
newProcedure hdeps pn@(ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    (_,recdict) <- tcProve l "newProc head" $ addHeadTCstrs hdeps
    addHeadTDict recdict
    i <- newTyVarId
    frees <- getFrees
    d' <- substFromTDict "newProc head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] mempty Set.empty mempty frees [] d'
    let rece = EntryEnv l recdt
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i rece . maybe Map.empty id) n (procedures env) }
    dirtyGDependencies $ Right $ Left $ Left $ funit pn
    
    solve l
    dict <- liftM (head . tDict) State.get
    d'' <- substFromTDict "newProc body" l dict False Map.empty d'
    let dt = DecT $ DecType i False [] mempty Set.empty mempty Set.empty [] d''
    let e = EntryEnv l dt
--    liftIO $ putStrLn $ "addProc " ++ ppr (entryType e)
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }
    return $ updLoc pn (Typed (unTyped $ loc pn) dt)
  
 -- | Checks that a procedure exists.
checkProcedure :: (MonadIO m,Location loc) => ProcedureName VarIdentifier loc -> TcM loc m [EntryEnv loc]
checkProcedure pn@(ProcedureName l n) = do
    addGDependencies $ Right $ Left $ Left $ funit pn
    ps <- liftM procedures State.get
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ Halt $ NotDefinedProcedure (pp n)
        Just es -> return $ Map.elems es

-- adds a recursive declaration for processing recursive constraints
withTpltDecRec :: (MonadIO m,Location loc) => loc -> DecType -> TcM loc m a -> TcM loc m a
withTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs p@(ProcType _ n@(Left (ProcedureName _ pn)) _ _ _ _)) m = do
    j <- newTyVarId
    let recd = DecType j True ts hd hfrees mempty bfrees specs p
    let rece = EntryEnv l (DecT recd)
    State.modify $ \env -> env { procedures = Map.alter (Just . Map.insert j rece . maybe Map.empty id) pn (procedures env) }
    x <- m
    State.modify $ \env -> env { procedures = Map.alter (Just . Map.delete j . maybe Map.empty id) pn (procedures env) }
    return x
withTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs p@(ProcType _ n@(Right op) _ _ _ _)) m = do
    j <- newTyVarId
    let o = funit op
    let recd = DecType j True ts hd hfrees mempty bfrees specs p
    let rece = EntryEnv l (DecT recd)
    State.modify $ \env -> env { operators = Map.alter (Just . Map.insert j rece . maybe Map.empty id) o (operators env) }
    x <- m
    State.modify $ \env -> env { operators = Map.alter (Just . Map.delete j . maybe Map.empty id) o (operators env) }
    return x
withTpltDecRec l d@(DecType i _ ts hd hfrees bd bfrees specs s@(StructType _ (TypeName _ sn) _)) m = do
    j <- newTyVarId
    let recd = DecType j True ts hd hfrees mempty bfrees specs s
    (e,es) <- liftM ((!sn) . structs) State.get
    let rece = EntryEnv l (DecT recd)
    State.modify $ \env -> env { structs = Map.alter (Just . (\(e,es) -> (e,Map.insert j rece es)) . fromJust) sn (structs env) }
    x <- m
    State.modify $ \env -> env { structs = Map.alter (Just . (\(e,es) -> (e,Map.delete j es)) . fromJust) sn (structs env) }
    return x
            

buildCstrGraph :: MonadIO m => Set (Loc loc IOCstr) -> TcM loc m (IOCstrGraph loc)
buildCstrGraph cstrs = do
    gr <- liftM (tCstrs . mconcat . tDict) State.get
    let tgr = Graph.trc gr 
    opens <- liftM openedCstrs State.get
    let cs = Set.difference (mapSet unLoc cstrs) (Set.fromList opens)
    let gr' = Graph.nfilter (\n -> any (\h -> Graph.hasEdge tgr (n,ioCstrId h)) cs) tgr
    return gr'
    
splitHead :: (Location loc,MonadIO m,Vars VarIdentifier (TcM loc m) loc) => Set (Loc loc IOCstr) -> TcM loc m (TDict loc,Set VarIdentifier,TDict loc,Set VarIdentifier)
splitHead deps = do
    d <- liftM (head . tDict) State.get
    frees <- getFrees
    hvs <- liftM Map.keysSet $ fvs $ Set.map (kCstr . unLoc) deps
    let hfrees = Set.intersection frees hvs
    let bfrees = Set.difference frees hfrees
    opens <- liftM openedCstrs State.get
    let cs = Set.difference (mapSet unLoc deps) (Set.fromList opens)
    let gr = Graph.trc $ tCstrs d
    let hgr = Graph.nfilter (\n -> any (\h -> Graph.hasEdge gr (n,ioCstrId h)) cs) gr
    let bgr = Graph.nfilter (\n -> not $ any (\h -> Graph.hasEdge gr (n,ioCstrId h)) cs) gr
    return (TDict hgr (tChoices d) (tSubsts d),hfrees,TDict bgr Set.empty Map.empty,bfrees)
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> Deps loc -> TypeName VarIdentifier (Typed loc) -> TcM loc m (TypeName VarIdentifier (Typed loc))
addTemplateStruct vars hdeps tn@(TypeName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees [] d
    dt' <- substFromTSubsts "templateStruct" l (tSubsts hdict `Map.union` tSubsts bdict) False Map.empty dt
    let e = EntryEnv l dt'
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStructTemplate (pp n) (locpos $ loc base)
        Nothing -> modify $ \env -> env { structs = Map.insert n (e,Map.empty) (structs env) }
    return $ updLoc tn (Typed (unTyped $ loc tn) dt')
    
-- Adds a new (possibly overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStructSpecialization :: (ProverK loc m) => [(Cond (VarName VarIdentifier Type),IsVariadic)] -> [(Type,IsVariadic)] -> Deps loc -> TypeName VarIdentifier (Typed loc) -> TcM loc m (TypeName VarIdentifier (Typed loc))
addTemplateStructSpecialization vars specials hdeps tn@(TypeName (Typed l t) n) = do
    d <- typeToDecType l t
    solve l
    (hdict,hfrees,bdict,bfrees) <- splitHead hdeps
    i <- newTyVarId
    let dt = DecT $ DecType i False vars (noTSubsts hdict) hfrees (noTSubsts bdict) bfrees specials d
    dt' <- substFromTSubsts "templateStructSpec" l (tSubsts hdict `Map.union` tSubsts bdict) False Map.empty dt
    let e = EntryEnv l dt'
    let mergeStructs (b1,s1) (b2,s2) = (b2,s1 `Map.union` s2)
    modify $ \env -> env { structs = Map.update (\(b,s) -> Just (b,Map.insert i e s)) n (structs env) }
    return $ updLoc tn (Typed (unTyped $ loc tn) dt')

-- | Defines a new struct type
newStruct :: (ProverK loc m) => Deps loc -> TypeName VarIdentifier (Typed loc) -> TcM loc m (TypeName VarIdentifier (Typed loc))
newStruct hdeps tn@(TypeName (Typed l t) n) = do
    addGDependencies $ Right $ Right $ funit tn
    d <- typeToDecType l t
    -- solve head constraints
    (_,recdict) <- tcProve l "newStruct head" $ addHeadTCstrs hdeps
    addHeadTDict recdict
    i <- newTyVarId
    -- add a temporary declaration for recursive invocations
    frees <- getFrees
    d' <- substFromTDict "newStruct head" l recdict False Map.empty d
    let recdt = DecT $ DecType i True [] mempty Set.empty mempty frees [] d'
    let rece = EntryEnv l recdt
    modify $ \env -> env { structs = Map.insert n (rece,Map.empty) (structs env) }
    dirtyGDependencies $ Right $ Right $ funit tn
    
    -- solve the body
    solve l
    dict <- liftM (head . tDict) State.get
    ss <- liftM structs get
    case Map.lookup n ss of
        Just (base,es) -> tcError (locpos l) $ MultipleDefinedStruct (pp n) (locpos $ entryLoc base)
        Nothing -> do
            i <- newTyVarId
            d'' <- substFromTDict "newStruct body" l dict False Map.empty d'
            let dt = DecT $ DecType i False [] mempty Set.empty mempty Set.empty [] d''
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
    mapM_ (dirtyGDependencies . Left . fst) $ Map.toList ss

addSubstM :: (ProverK loc m) => loc -> VarName VarIdentifier Type -> Type -> TcM loc m ()
addSubstM l v t | varNameToType v == t = return ()
addSubstM l v t = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
    tcCstrM l $ Unifies (loc v) (tyOf t)
    addSubst l (varNameId v) t
    dirtyGDependencies $ Left $ varNameId v
    
--addSubstM l v t | varNameToType v == t = return ()
--                | typeClass "addSubstML" (varNameToType v) == typeClass "addSubstMR" t = do
--                    addSubst l (varNameId v) t
--                    dirtyVarDependencies (varNameId v)
--                | otherwise = genTcError (locpos l) $ text "Variable" <+> quotes (pp v) <+> text "does not match type" <+> quotes (pp t)

newDomainTyVar :: (MonadIO m,Location loc) => SVarKind -> Maybe Doc -> TcM loc m SecType
newDomainTyVar k doc = do
    n <- uniqVarId "d" doc
    return $ SVar n k

newDimVar :: (MonadIO m,Location loc) => Maybe Doc -> TcM loc m (SExpr VarIdentifier Type)
newDimVar doc = do
    n <- uniqVarId "dim" doc
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newTypedVar :: (MonadIO m,Location loc) => String -> a -> Maybe Doc -> TcM loc m (VarName VarIdentifier a)
newTypedVar s t doc = liftM (VarName t) $ uniqVarId s doc

newVarOf :: (MonadIO m,Location loc) => String -> Type -> Maybe Doc -> TcM loc m Type
newVarOf str TType doc = newTyVar doc
newVarOf str BType doc = liftM BaseT $ newBaseTyVar doc
newVarOf str (SType k) doc = liftM SecT $ newDomainTyVar k doc
newVarOf str t doc | typeClass "newVarOf" t == TypeC = liftM (IdxT . varExpr) $ newTypedVar str t doc
newVarOf str (VAType b sz) doc = liftM VArrayT $ newArrayVar b sz doc

newArrayVar :: (MonadIO m,Location loc) => Type -> SExpr VarIdentifier Type -> Maybe Doc -> TcM loc m VArrayType
newArrayVar b sz doc = do
    n <- uniqVarId "varr" doc
    return $ VAVar n b sz

newTyVar :: (MonadIO m,Location loc) => Maybe Doc -> TcM loc m Type
newTyVar doc = do
    n <- uniqVarId "t" doc
    return $ ComplexT $ CVar n

newDecVar :: (MonadIO m,Location loc) => Maybe Doc -> TcM loc m DecType
newDecVar doc = do
    n <- uniqVarId "dec" doc
    return $ DVar n
    
newBaseTyVar :: (MonadIO m,Location loc) => Maybe Doc -> TcM loc m BaseType
newBaseTyVar doc = do
    n <- uniqVarId "b" doc
    return $ BVar n

newIdxVar :: (MonadIO m,Location loc) => Maybe Doc -> TcM loc m (VarName VarIdentifier Type)
newIdxVar doc = do
    n <- uniqVarId "idx" doc
    let v = VarName (BaseT index) n
    return v
    
newSizeVar :: (MonadIO m,Location loc) => Maybe Doc -> TcM loc m (SExpr VarIdentifier Type)
newSizeVar doc = do
    n <- uniqVarId "sz" doc
    let v = VarName (BaseT index) n
    return (RVariablePExpr (BaseT index) v)

newSizesVar :: (MonadIO m,Location loc) => SExpr VarIdentifier Type -> Maybe Doc -> TcM loc m [(SExpr VarIdentifier Type,IsVariadic)]
newSizesVar dim doc = do
    n <- uniqVarId "szs" doc
    let t = VAType (BaseT index) dim
    let v = VarName t n
    return [(RVariablePExpr t v,True)]
    
mkVariadicTyArray :: (MonadIO m,Location loc) => IsVariadic -> Type -> TcM loc m Type
mkVariadicTyArray False t = return t
mkVariadicTyArray True t = do
    sz <- newSizeVar Nothing
    return $ VAType t sz
    
addValue :: (MonadIO m,Location loc) => loc -> VarIdentifier -> SExpr VarIdentifier Type -> TcM loc m ()
addValue l v e = do
--    liftIO $ putStrLn $ "addValue " ++ ppr v ++ " " ++ ppr e
    updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert v (IdxT e) (tSubsts d) })

addValueM :: (ProverK loc m) => Bool -> loc -> VarName VarIdentifier Type -> SExpr VarIdentifier Type -> TcM loc m ()
addValueM checkTy l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
addValueM checkTy l v@(VarName t n) e = addErrorM l (TypecheckerError (locpos l) . MismatchingVariableType (pp v)) $ do
    when checkTy $ tcCstrM l $ Unifies t (loc e)
    addValue l n e
    addGDependencies $ Left n
    dirtyGDependencies $ Left n

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
    gr <- liftM (tCstrs . head . tDict) State.get
    case contextGr gr (ioCstrId iok) of
        Nothing -> return ()
        Just (deps,_,_,_) -> forM_ deps $ \(_,d) -> case lab gr d of
            Nothing -> return ()
            Just x -> addIODependency (unLoc x) (Set.singleton iok)

-- | adds a dependency on the given variable for all the opened constraints
addGDependencies :: (MonadIO m,Location loc) => GIdentifier -> TcM loc m ()
addGDependencies v = do
    cstrs <- liftM openedCstrs State.get
    addGDependency v cstrs
    
addGDependency :: (MonadIO m,Location loc) => GIdentifier -> [IOCstr] -> TcM loc m ()
addGDependency v cstrs = do
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

addHeadTCstrs :: (Monad m,Location loc) => Set (Loc loc IOCstr) -> TcM loc m ()
addHeadTCstrs ks = addHeadTDict $ TDict (Graph.mkGraph nodes []) Set.empty Map.empty
    where nodes = map (\n -> (ioCstrId $ unLoc n,n)) $ Set.toList ks

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
    (x,d') <- updHeadM upd (tDict e)
    let e' = e { tDict = d' }
    State.put e'
    return x

-- | forget the result for a constraint when the value of a variable it depends on changes
dirtyGDependencies :: (MonadIO m,Location loc) => GIdentifier -> TcM loc m ()
dirtyGDependencies v = do
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
    vi' <- uniqVarId vi Nothing
    case scope of
        LocalScope -> State.modify $ \env -> env { localConsts = Map.insert vi vi' $ localConsts env }
        GlobalScope -> State.modify $ \env -> env { globalConsts = Map.insert vi vi' $ globalConsts env }
--    addFree vi'
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
isChoice x = liftM (Set.member (hashUnique x) . tChoices . mconcat . tDict) State.get

addChoice :: (Monad m,Location loc) => Unique -> TcM loc m ()
addChoice x = updateHeadTDict $ \d -> return ((),d { tChoices = Set.insert (hashUnique x) $ tChoices d })

bytes :: ComplexType
bytes = CType Public (TyPrim $ DatatypeUint8 ()) (indexSExpr 1)


substFromTDict :: (VarsIdTcM loc m,Location loc,VarsId (TcM loc m) a) => String -> loc -> TDict loc -> Bool -> Map VarIdentifier VarIdentifier -> a -> TcM loc m a
substFromTDict msg l dict doBounds ssBounds = substFromTSubsts msg l (tSubsts dict) doBounds ssBounds

substFromTSubsts :: (VarsIdTcM loc m,Location loc,VarsId (TcM loc m) a) => String -> loc -> TSubsts -> Bool -> Map VarIdentifier VarIdentifier -> a -> TcM loc m a
substFromTSubsts msg l tys doBounds ssBounds = substProxy msg (substsProxyFromTSubsts l tys) doBounds ssBounds 
    
substsProxyFromTSubsts :: (Location loc,Typeable loc,Monad m) => loc -> TSubsts -> SubstsProxy VarIdentifier (TcM loc m)
substsProxyFromTSubsts (l::loc) tys = SubstsProxy $ \proxy x -> do
    case Map.lookup x tys of
        Nothing -> return Nothing
        Just ty -> case proxy of
            (eq (typeRep :: TypeOf (VarName VarIdentifier Type)) -> EqT) ->
                return $ typeToVarName ty
            (eq (typeRep :: TypeOf (SecTypeSpecifier VarIdentifier (Typed loc))) -> EqT) ->
                case ty of
                    SecT s -> liftM Just $ secType2SecTypeSpecifier s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (VarName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToVarName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier Type)) -> EqT) ->
                return $ typeToDomainName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier ())) -> EqT) ->
                return $ fmap funit $ typeToDomainName ty
            (eq (typeRep :: TypeOf (DomainName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToDomainName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier Type)) -> EqT) ->
                return $ typeToTypeName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier ())) -> EqT) ->
                return $ fmap funit $ typeToTypeName ty
            (eq (typeRep :: TypeOf (TypeName VarIdentifier (Typed loc))) -> EqT) ->
                return $ fmap (fmap (Typed l)) $ typeToTypeName ty
            (eq (typeRep :: TypeOf SecType) -> EqT) ->
                case ty of
                    SecT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf VArrayType) -> EqT) ->
                case ty of
                    VArrayT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf DecType) -> EqT) ->
                case ty of
                    DecT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf ComplexType) -> EqT) ->
                case ty of
                    ComplexT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf BaseType) -> EqT) ->
                case ty of
                    BaseT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (Expression VarIdentifier Type)) -> EqT) ->
                case ty of
                    IdxT s -> return $ Just s
                    otherwise -> return Nothing
            (eq (typeRep :: TypeOf (Expression VarIdentifier (Typed loc))) -> EqT) ->
                case ty of
                    IdxT s -> return $ Just $ fmap (Typed l) s
                    otherwise -> return Nothing
            otherwise -> return Nothing
  where
    eq x proxy = eqTypeOf x (typeOfProxy proxy)
    
specializeM :: (VarsId (TcM loc m) a,VarsIdTcM loc m,Location loc) => loc -> a -> TcM loc m a
specializeM l a = do
    ss <- getTSubsts
    substFromTSubsts "specialize" l ss False Map.empty a

ppM :: (VarsId (TcM loc m) a,VarsIdTcM loc m,PP a,Location loc) => loc -> a -> TcM loc m Doc
ppM l a = liftM pp $ specializeM l a

ppArrayRangesM :: (VarsIdTcM loc m,Location loc) => loc -> [ArrayProj] -> TcM loc m Doc
ppArrayRangesM l = liftM (sepBy comma) . mapM (ppM l)

removeTSubsts :: Monad m => Set VarIdentifier -> TcM loc m ()
removeTSubsts vs = do
    env <- State.get
    let ds = tDict env
    let remSub d = d { tSubsts = Map.difference (tSubsts d) (Map.fromSet (const $ NoType "rem") vs) }
    let ds' = map remSub ds
    State.put $ env { tDict = ds' }



