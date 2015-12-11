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
        [e] -> return $ entryType e 
        es -> tcError (locpos l) $ NoNonTemplateType (ppVarId n)

-- | Checks if a template type exists in scope
-- Returns all template type declarations in scope, base template first
checkTemplateType :: Location loc => TypeName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkTemplateType ty@(TypeName _ n) = do
    es <- checkType ty
    let check e = case entryType e of
                    TType -> return ()
                    BType -> return ()
                    otherwise -> tcError (locpos $ loc ty) $ NoTemplateType (ppVarId n) (locpos $ entryLoc e)
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
            [e] -> case entryType e of
                DecT (TpltType {}) -> tcError (locpos l) $ NoNonTemplateType (ppVarId vn)
                t -> return t
            es -> tcError (locpos l) $ NoNonTemplateType (ppVarId vn)
        (Nothing,Just e,Nothing) -> return $ entryType e
        (Nothing,Nothing,Just e) -> return $ entryType e
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

-- | Adds a new (possibly overloaded) template operator to the environment
-- adds the template constraints
addTemplateOperator :: (VarsTcM loc,Location loc) => [VarName VarIdentifier Type] -> Op VarIdentifier (Typed loc) -> TcM loc ()
addTemplateOperator vars op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    let o = fmap (const ()) op
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] d) UnknownValue
    modify $ \env -> env { operators = Map.alter (Just . Map.insert i e . maybe Map.empty id) o (operators env) }

-- | Adds a new (possibly overloaded) operator to the environment.
newOperator :: (VarsTcM loc,Location loc) => Op VarIdentifier (Typed loc) -> TcM loc ()
newOperator op = do
    let Typed l t = loc op
    d <- typeToDecType l t
    let o = fmap (const ()) op
    let e = EntryEnv l t UnknownValue
    modify $ \env -> env { operators = Map.alter (Just . Map.insert (decTypeTyVarId d) e . maybe Map.empty id) o (operators env) }
  
 -- | Checks that an oeprator exists.
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
        Nothing -> tcError (locpos $ loc op) $ NotDefinedOperator $ pp cop
        Just es -> return $ Map.elems es
  
-- | Adds a new (possibly overloaded) template procedure to the environment
-- adds the template constraints
addTemplateProcedure :: (VarsTcM loc,Location loc) => [VarName VarIdentifier Type] -> ProcedureName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateProcedure vars (ProcedureName (Typed l t) n) = do
    dt <- typeToDecType l t
    cstrs <- liftM (headNe . tDict) get
    i <- newTyVarId
    let e = EntryEnv l (DecT $ TpltType i vars (fmap locpos cstrs) [] dt) UnknownValue
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert i e . maybe Map.empty id) n (procedures env) }

-- | Adds a new (possibly overloaded) procedure to the environment.
newProcedure :: (VarsTcM loc,Location loc) => ProcedureName VarIdentifier (Typed loc) -> TcM loc ()
newProcedure (ProcedureName (Typed l t) n) = do
    d <- typeToDecType l t
    let e = EntryEnv l t UnknownValue
    modify $ \env -> env { procedures = Map.alter (Just . Map.insert (decTypeTyVarId d) e . maybe Map.empty id) n (procedures env) }
  
 -- | Checks that a procedure exists.
checkProcedure :: Location loc => ProcedureName VarIdentifier loc -> TcM loc [EntryEnv loc]
checkProcedure (ProcedureName l n) = do
    ps <- liftM procedures State.get
    case Map.lookup n ps of
        Nothing -> tcError (locpos l) $ NotDefinedProcedure (ppVarId n)
        Just es -> return $ Map.elems es
    
-- Adds a new (non-overloaded) template structure to the environment.
-- Adds the template constraints from the environment
addTemplateStruct :: (VarsTcM loc,Location loc) => [VarName VarIdentifier Type] -> TypeName VarIdentifier (Typed loc) -> TcM loc ()
addTemplateStruct vars (TypeName (Typed l t) n) = do
    struct <- typeToDecType l t
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
    updateHeadTDict $ \d -> return ((),mappend d (TDict Map.empty ss))
    mapM_ (uncurry dirtyVarDependencies) $ Map.toList ss

---- | Adds a new template constraint to the environment
newTemplateConstraint :: Location loc => loc -> TCstr -> TcM loc IOCstr
newTemplateConstraint l c = do
    updateHeadTDict (insertTDictCstr l c Unevaluated)

addSubstM :: Location loc => loc -> VarName VarIdentifier Type -> Type -> TcM loc ()
addSubstM l v t | varNameToType v == t = return ()
                | typeClass "addSubstML" (varNameToType v) == typeClass "addSubstMR" t = do
                    updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert (fmap (const ()) v) t (tSubsts d) })
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
    
uniqVarId :: Identifier -> TcM loc VarIdentifier
uniqVarId n = do
    i <- newTyVarId
    return $ VarIdentifier n (Just i)
    
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
    
addValueM :: Location loc => loc -> VarName VarIdentifier (Typed loc) -> Expression VarIdentifier (Typed loc) -> TcM loc ()
addValueM l (VarName t n) (RVariablePExpr _ (VarName _ ((==n) -> True))) = return ()
addValueM l (VarName t n) e | typeClass "addValueL" (typed t) == typeClass "addValueR" (typed $ loc e) = do
    updateHeadTDict $ \d -> return ((),d { tSubsts = Map.insert (VarName () n) (IdxT $ fmap typed e) (tSubsts d) })
    dirtyVarDependencies (VarName () n) (IdxT $ fmap typed e)
addValueM l v e = genericError (locpos l) $ text "unification: mismatching expression types"

resolveCstr :: Location loc => loc -> TCstr -> (loc -> TCstr -> TcM loc Type) -> TcM loc Type
resolveCstr l k resolve = do
    dict <- liftM (headNe . tDict) State.get
    iok <- updateHeadTDict (insertTDictCstr l k Unevaluated)
    resolveIOCstr l iok resolve

openCstr l iok = do
    opts <- TcM $ lift ask
    size <- liftM (length . openedCstrs) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded (constraintStackSize opts)
        else State.modify $ \e -> e { openedCstrs = iok : openedCstrs e }

newDict l = do
    opts <- TcM $ lift ask
    size <- liftM (lengthNe . tDict) State.get
    if size >= constraintStackSize opts
        then tcError (locpos l) $ ConstraintStackSizeExceeded (constraintStackSize opts)
        else State.modify $ \e -> e { tDict = ConsNe mempty (tDict e) }

resolveIOCstr :: Location loc => loc -> IOCstr -> (loc -> TCstr -> TcM loc Type) -> TcM loc Type
resolveIOCstr l iok resolve = do
    st <- liftIO $ readUniqRef (kStatus iok)
    case st of
        Evaluated t -> return t
        Erroneous err -> throwError err
        Unevaluated -> do
            openCstr l iok
            t <- resolve l $ kCstr iok
            liftIO $ writeUniqRef (kStatus iok) (Evaluated t)
            State.modify $ \e -> e { openedCstrs = List.delete iok (openedCstrs e) } 
            updateHeadTDict $ \d -> return ((),d { tCstrs = Map.delete (uniqId $ kStatus iok) (tCstrs d) })
            return t

-- | adds a dependency on the given variable for all the opened constraints
addVarDependencies :: Location loc => VarName VarIdentifier () -> TcM loc ()
addVarDependencies v = do
    cstrs <- liftM openedCstrs State.get
    liftIO $ modifyIORef' globalEnv $ \g -> g { tDeps = Map.insertWith (++) v cstrs (tDeps g) }

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
    case Map.lookup v deps of
        Nothing -> return ()
        Just ios -> do
--            liftIO $ putStrLn $ "deps " ++ show (map (show . hashUnique . uniqId . kStatus) ios)
--            liftIO $ putStrLn $ "opens " ++ show (map (show . hashUnique . uniqId . kStatus) cstrs)
            let dirty x = unless (elem x cstrs) $ do
--                liftIO $ putStrLn $ "dirty " ++ show (hashUnique $ uniqId $ kStatus x)
                liftIO $ writeUniqRef (kStatus x) Unevaluated
            mapM_ dirty ios

vars env = Map.union (localVars env) (globalVars env)

getTSubsts :: Location loc => TcM loc TSubsts
getTSubsts = do
    env <- State.get
    let es = Map.foldrWithKey (\k e m -> case entryValue e of { KnownExpression ex -> Map.insert (VarName () k) (IdxT $ fmap typed ex) m; otherwise -> m}) Map.empty $ vars env
    let sst = tSubsts $ mconcatNe $ tDict env
    return $ Map.unions [es,sst]



