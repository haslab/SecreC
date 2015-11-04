module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Utils
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint

import Data.Typeable
import Data.Maybe
import qualified Data.Map as Map

import Control.Monad
import Control.Monad.IO.Class

-- Left = type template
-- Right = procedure overload
type TIdentifier = Either Identifier Identifier

tId :: TIdentifier -> Identifier
tId = either id id

-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: Location loc => loc -> TIdentifier -> [Type] -> Maybe Type -> TcReaderM loc [EntryEnv loc] -> TcM loc (Type,Type)
matchTemplate l n args ret check = do
    entries <- tcReaderM $ check
    instances <- instantiateTemplateEntries n args ret entries
    case instances of
        [] -> tcError (locpos l) $ NoMatchingTemplateOrProcedure (tId n) (map (locpos . entryLoc) entries)
        es -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,subst):_) <- sortByM (compareTemplateDecls l n) es
            -- return the instantiated body of the most specific declaration
            resolveTemplateEntry n args ret e subst

-- | Matches a list of constraints and produces a dictionary as a witness
resolveTemplateConstraints :: Location loc => loc -> TDict -> TcM loc ()
resolveTemplateConstraints l (TDict cstrs) = do
    let ks = Map.keys $ Map.filter isNothing cstrs
    mapM_ resolveCstr ks
  where
    resolveCstr t = tcProofM $ resolveTCstr l t >> return ()

resolveTemplateEntry :: Location loc => TIdentifier -> [Type] -> Maybe Type -> EntryEnv loc -> Substs Type -> TcM loc (Type,Type)
resolveTemplateEntry n args ret e s = case entryType e of
    TpltType _ vars cstrs specials body -> do
        let cstrs' = subst s cstrs -- specialize the constraints
        let specials' = substTraversable s specials -- specialize the specializations
        let body' = subst s body -- specialize the struct or procedure body
        -- add the constraints first because of possibly recursive invocations
        case n of
            Left i -> do
                addTemplateConstraint (TApp i args) (Just body')
                addTemplateConstraint (TDec i args) (Just $ entryType e)
            Right i -> do
                addTemplateConstraint (PApp i args ret) (Just body')
                addTemplateConstraint (PDec i args ret) (Just $ entryType e)
        resolveTemplateConstraints (entryLoc e) cstrs' -- compute a dictionary from the constraints
        let body'' = case body' of
                        ProcType _ _ _ ret -> ret
                        ret -> ret
        return (body'',entryType e)

-- | Tells if one declaration is strictly more specific than another, and if not it fails
compareTemplateDecls :: Location loc => loc -> TIdentifier -> (EntryEnv loc,Substs Type) -> (EntryEnv loc,Substs Type) -> TcM loc Ordering
compareTemplateDecls l n (e1,s1) (e2,d2) = do
    e1' <- localTemplate e1
    e2' <- localTemplate e2
    targs1 <- templateArgs n e1'
    targs2 <- templateArgs n e2'
    (ord,_) <- tcProofM $ comparesList l targs1 targs2
    when (ord == EQ) $ tcError (locpos l) $ ComparisonException $ "Duplicate instances for template or overload" ++ tId n
    return ord
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: Location loc => TIdentifier -> [Type] -> Maybe Type -> [EntryEnv loc] -> TcM loc [(EntryEnv loc,Substs Type)]
instantiateTemplateEntries n args ret es = foldM (\xs e -> liftM (xs ++) (instantiateTemplateEntry n args ret e)) [] es

instantiateTemplateEntry :: Location loc => TIdentifier -> [Type] -> Maybe Type -> EntryEnv loc -> TcM loc [(EntryEnv loc,Substs Type)]
instantiateTemplateEntry n args mbret e = do
    ret <- maybe newTyVar return mbret -- generate a new type variable if the return type is not known
    e' <- localTemplate e
    targs <- templateArgs n e'
    ok <- prove (unifiesList (entryLoc e) (args ++ [ret]) targs)
    case ok of
        Nothing -> return []
        Just ((),subst) -> return [(e,subst)]
        
-- | Creates a distinct head signature from a template type declaration
-- Rename variables to make sure that they are unique to this signature
templateArgs :: Location loc => TIdentifier -> EntryEnv loc -> TcM loc [Type]
templateArgs (Left name) e = case entryType e of
    TpltType _ args cstrs [] body -> return $ map TVar args -- a base template uses the base arguments
    TpltType _ args cstrs specials body -> return specials -- a specialization uses the specialized arguments
templateArgs (Right name) e = case entryType e of
    TpltType _ args cstrs [] (ProcType _ _ vars ret) -> do -- include the return type
        return $ map (\(VarName t n) -> t) vars ++ [ret]
    ProcType _ _ vars ret -> do -- include the return type
        return $ map (\(VarName t n) -> t) vars ++ [ret]
    otherwise -> genericError (locpos $ entryLoc e) "Invalid type for procedure template"

-- | renames the variables in a template to local names
localTemplate :: Location loc => EntryEnv loc -> TcM loc (EntryEnv loc)
localTemplate e = case entryType e of
    TpltType _ args cstrs specials body -> do
        s <- mapM uniqueVar args
        return $ EntryEnv (entryLoc e) (subst (substFromList proxy s) (entryType e))
    t -> return e
  where
    uniqueVar i@(Typed v t) = newTyVarId >>= \j -> return (i,TVar $ Typed (Right j) t)
    proxy = Proxy :: Proxy Type

