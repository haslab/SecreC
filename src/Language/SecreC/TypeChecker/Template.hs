{-# LANGUAGE ScopedTypeVariables #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Error
import Language.SecreC.Utils
import Language.SecreC.Pretty
import {-# SOURCE #-} Language.SecreC.TypeChecker.Constraint

import Data.Typeable
import Data.Either
import Data.Maybe
import qualified Data.Map as Map

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import qualified Control.Monad.State as State

import Text.PrettyPrint

-- | Matches a list of template arguments against a list of template declarations
matchTemplate :: (Vars loc,Location loc) => loc -> TIdentifier -> [Type] -> Maybe Type -> TcM loc [EntryEnv loc] -> TcM loc (Type,Type)
matchTemplate l n args ret check = do
    entries <- check
    instances <- instantiateTemplateEntries n args ret entries
    let def = ppTpltApp n args ret
    let oks = rights instances
    let errs = lefts instances
    case oks of
        [] -> do
            let defs = map (\(e,err) -> (locpos $ entryLoc e,ppTpltType n (entryType e),err)) errs
            ss <- liftM ppSubstsGeneric getSubstsGeneric
            tcError (locpos l) $ NoMatchingTemplateOrProcedure def defs ss
        es -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,subst):_) <- sortByM (compareTemplateDecls def l n) es
            -- return the instantiated body of the most specific declaration
            resolveTemplateEntry l n args ret e subst

templateCstrs :: Location loc => loc -> TDict loc -> TDict loc
templateCstrs p d = d { tCstrs = Map.mapKeys (\(Loc l k) -> Loc l $ DelayedCstr k (TypecheckerError (locpos p) . TemplateSolvingError)) (tCstrs d) }

--inheritedTDict :: Location loc => loc -> TDict loc -> TDict loc
--inheritedTDict l d = d { tCstrs = Map.mapKeys (\(Loc l1 c) -> Loc l $ InheritedCstr (locpos l1) c) (tCstrs d) }

resolveTemplateEntry :: (Vars loc,Location loc) => loc -> TIdentifier -> [Type] -> Maybe Type -> EntryEnv loc -> TDict loc -> TcM loc (Type,Type)
resolveTemplateEntry p n args ret (e :: EntryEnv loc) dict = do
    let l = entryLoc e
    let sub :: Vars a => a -> a
        sub = substFromTDict dict
    let dict' = (sub dict) -- specialize the dictionary with its own substitutions
    addDict dict'
    case entryType e of
        TpltType _ _ cstrs _ body -> do
            let cstrs' = fmap (updpos l) $ sub $ templateCstrs (locpos p) cstrs
            let body' = sub body
            -- add the constraints first because of possibly recursive invocations
            case n of
                Left i -> do
                    addTemplateConstraint l (TApp i args) (Just body')
                    addTemplateConstraint l (TDec i args) (Just $ entryType e)
                Right i -> do
                    addTemplateConstraint l (PDec i args $ fromJust ret) (Just $ entryType e)
            --liftIO $ putStrLn $ "FROM TEMPLATE " ++ show (vcat $ map pp $ tUnsolved cstrs')
            addDict cstrs' -- add the constraints to the environment
            let body'' = case body' of
                            ProcType _ _ _ ret stmts -> ret
                            ret -> ret
            return (body'',entryType e)
        ProcType _ _ _ body stmts -> do
            let body' = sub body
            case n of
                Right i -> do
                    addTemplateConstraint l (PDec i args $ fromJust ret) (Just $ entryType e)
            return (body',entryType e)
        t -> error $ "resolveTemplateEntry: " ++ show t

-- | Tells if one declaration is strictly more specific than another, and if not it fails
compareTemplateDecls :: (Vars loc,Location loc) => Doc -> loc -> TIdentifier -> (EntryEnv loc,TDict loc) -> (EntryEnv loc,TDict loc) -> TcM loc Ordering
compareTemplateDecls def l n (e1,s1) (e2,d2) = tcBlock $ do
    e1' <- localTemplate e1
    e2' <- localTemplate e2
    targs1 <- templateArgs n e1'
    targs2 <- templateArgs n e2'
    let defs = map (\e -> (locpos $ entryLoc e,ppTpltType n (entryType e))) [e1,e2]
    let err = TypecheckerError (locpos l) . ConflictingTemplateInstances def defs
    ord <- addErrorM err $ comparesList l targs1 targs2
    when (ord == EQ) $ do
        ss <- liftM ppSubstsGeneric getSubstsGeneric
        tcError (locpos l) $ DuplicateTemplateInstances def defs ss
    return ord
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (Vars loc,Location loc) => TIdentifier -> [Type] -> Maybe Type -> [EntryEnv loc] -> TcM loc [Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc)]
instantiateTemplateEntries n args ret es = mapM (instantiateTemplateEntry n args ret) es

instantiateTemplateEntry :: (Vars loc,Location loc) => TIdentifier -> [Type] -> Maybe Type -> EntryEnv loc -> TcM loc (Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc))
instantiateTemplateEntry n args ret e = do
    let l = entryLoc e
    e' <- localTemplate e
    targs <- templateArgs n e'
    let proof = case ret of
                Nothing -> coercesList l args targs
                Just r -> coercesList l args (init targs) >> unifies l r (last targs)
    ok <- prove proof
    case ok of
        Left err -> return $ Left (e',err)
        Right ((),subst) -> do
            --ss <- liftM ppSubstsGeneric getSubstsGeneric
            --liftIO $ putStrLn $ "instantiated " ++ ppr n ++ " " ++ ppr args ++ " " ++ ppr ret ++ " " ++ ppr (entryType e') ++ "\n" ++ show ss ++  "INST\n" ++ ppr (tSubsts subst) ++ ppr (tValues subst)
            return $ Right (e',subst)
        
-- | Extracts a head signature from a template type declaration
templateArgs :: Location loc => TIdentifier -> EntryEnv loc -> TcM loc [Type]
templateArgs (Left name) e = case entryType e of
    TpltType _ args cstrs [] body -> return $ map TVar args -- a base template uses the base arguments
    TpltType _ args cstrs specials body -> return specials -- a specialization uses the specialized arguments
templateArgs (Right name) e = case entryType e of
    TpltType _ args cstrs [] (ProcType _ _ vars ret stmts) -> do -- include the return type
        return $ map (\(VarName t n) -> t) vars ++ [ret]
    ProcType _ _ vars ret stmts -> do -- include the return type
        return $ map (\(VarName t n) -> t) vars ++ [ret]
    otherwise -> genericError (locpos $ entryLoc e) "Invalid type for procedure template"

-- | renames the variables in a template to local names
localTemplate :: (Vars loc,Location loc) => EntryEnv loc -> TcM loc (EntryEnv loc)
localTemplate (e::EntryEnv loc) = case entryType e of
    TpltType tpltid args cstrs specials body -> do
        uniqs <- mapM uniqueVar args
        -- VarName VarIdentifier () --> Type
        let subt1 = substsFromList $ map (\(x,y) -> (x,TVar y)) uniqs
        -- VarName VarIdentifier () --> Expression VarIdentifier Type
        let subt2 = substsFromList $ map (\(x,y) -> (x,RVariablePExpr (loc y) y)) uniqs
        -- VarName VarIdentifier () --> Expression VarIdentifier (Typed loc)
        let subt3 = substsFromList $ map (\(x,y) -> (x,fmap (Typed l) $ RVariablePExpr (loc y) y)) uniqs
        -- VarName VarIdentifier () --> VarName VarIdentifier Type
        let subt4 = substsFromList uniqs
        let sub :: Vars a => a -> a
            sub = subst subt1 . subst subt2 . subst subt3 . subst subt4
        let body' = sub body
        let cstrs' = sub cstrs
        let specials' = sub specials
        let t' = TpltType tpltid (map snd uniqs) cstrs' specials' body'
        let v' = sub (entryValue e)
        return $ EntryEnv l t' v'
    t -> return e
  where
    uniqueVar :: VarName VarIdentifier Type -> TcM loc (VarName VarIdentifier (),VarName VarIdentifier Type)
    uniqueVar i@(VarName t v) = newTyVarId >>= \j -> return (VarName () v,VarName t (VarIdentifier (varIdBase v) $ Just j))
    l = entryLoc e

