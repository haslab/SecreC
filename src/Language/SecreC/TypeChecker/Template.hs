{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

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
matchTemplate :: (VarsTcM loc,Location loc) => loc -> TIdentifier -> [Type] -> Maybe Type -> TcM loc [EntryEnv loc] -> TcM loc Type
matchTemplate l n args ret check = do
    entries <- check
    instances <- instantiateTemplateEntries n args ret entries
    let def = ppTpltApp n args ret
    let oks = rights instances
    let errs = lefts instances
    case oks of
        [] -> do
            let defs = map (\(e,err) -> (locpos $ entryLoc e,ppTpltType (entryType e),err)) errs
            ss <- liftM ppTSubsts getTSubsts
            tcError (locpos l) $ NoMatchingTemplateOrProcedure def defs ss
        es -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,subst):_) <- sortByM (compareTemplateDecls def l n) es
            -- return the instantiated body of the most specific declaration
            resolveTemplateEntry l n args ret e subst

templateCstrs :: Location loc => Doc -> loc -> TDict loc -> TDict loc
templateCstrs doc p d = d { tCstrs = Map.map upd (tCstrs d) }
    where
    upd (Loc l k) = Loc l $ k { kCstr = DelayedCstr (kCstr k) (TypecheckerError (locpos p) . TemplateSolvingError doc) }

resolveTemplateEntry :: (VarsTcM loc,Location loc) => loc -> TIdentifier -> [Type] -> Maybe Type -> EntryEnv loc -> TDict loc -> TcM loc Type
resolveTemplateEntry p n args ret (e :: EntryEnv loc) dict = do
    let l = entryLoc e
    let sub :: Vars (TcM loc) a => a -> TcM loc a
        sub = substFromTDict dict
    dict' <- sub dict -- specialize the dictionary with its own substitutions
    addHeadTDict dict'
    case entryType e of
        DecT (TpltType a b cstrs specs body) -> do
            let ppApp = pp ret <+> pp n <+> sepBy comma (map pp args)
            cstrs' <- liftM (fmap (updpos l)) $ sub $ templateCstrs ppApp (locpos p) cstrs
            body' <- sub body
            specs' <- sub specs
            cstrs'' <- liftM snd $ tcProve l $ addHeadTDict cstrs'
            return $ DecT $ TpltType a b (fmap locpos cstrs'') specs' body'
        DecT (ProcType a b n args body stmts) -> do
            n' <- sub n
            body' <- sub body
            args' <- mapM sub args
            stmts' <- sub stmts
            return $ DecT $ ProcType a b n' args' body' stmts'
        t -> error $ "resolveTemplateEntry: " ++ show t

templateReturn :: (VarsTcM loc,Location loc) => loc -> Type -> TcM loc Type
templateReturn l (DecT d) = return $ templateDecReturn d
templateReturn l (TK k) = do
    t <- resolveTK l k
    templateReturn l t
templateReturn l t = genericError (locpos l) $ text "Unknown template return type for" <+> quotes (pp t)

templateDecReturn :: DecType -> Type
templateDecReturn (TpltType _ _ _ _ b) = templateDecReturn b
templateDecReturn (ProcType _ _ _ _ r _) = r
templateDecReturn s@(StructType {}) = DecT s

-- | Tells if one declaration is strictly more specific than another, and if not it fails.
-- Since we are unifying base types during instantiaton, it may happen that the most specific match is chosen over another more generic best match. This problem does not arise though if we only resolve templates on full instantiation. If we ever change this, we should use instead a three-way comparison that also tries to minimize the number of instantiated type variables in the context.
-- An example is if we tried to match the template over a type variable T:
-- y = f ((T) x)
-- bool f (int x) { ... }     (1)
-- bool f (T x) { ... }       (2)
-- bool f (T [[N]] x) { ... } (3)
-- We would be choosing choosing (1), even though the best match is in principle (2), that does not instantiate T.
compareTemplateDecls :: (VarsTcM loc,Location loc) => Doc -> loc -> TIdentifier -> (EntryEnv loc,TDict loc) -> (EntryEnv loc,TDict loc) -> TcM loc Ordering
compareTemplateDecls def l n (e1,s1) (e2,d2) = tcBlock $ do
    e1' <- localTemplate e1
    e2' <- localTemplate e2
    targs1 <- templateArgs n e1'
    targs2 <- templateArgs n e2'
    let defs = map (\e -> (locpos $ entryLoc e,ppTpltType (entryType e))) [e1,e2]
    let err = TypecheckerError (locpos l) . ConflictingTemplateInstances def defs
    ord <- addErrorM err $ comparesList l targs1 targs2
    when (ord == EQ) $ do
        ss <- liftM ppTSubsts getTSubsts
        tcError (locpos l) $ DuplicateTemplateInstances def defs ss
    return ord
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateEntries :: (VarsTcM loc,Location loc) => TIdentifier -> [Type] -> Maybe Type -> [EntryEnv loc] -> TcM loc [Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc)]
instantiateTemplateEntries n args ret es = mapM (instantiateTemplateEntry n args ret) es

instantiateTemplateEntry :: (VarsTcM loc,Location loc) => TIdentifier -> [Type] -> Maybe Type -> EntryEnv loc -> TcM loc (Either (EntryEnv loc,SecrecError) (EntryEnv loc,TDict loc))
instantiateTemplateEntry n args ret e = do
    let l = entryLoc e
    e' <- localTemplate e
    targs <- templateArgs n e'
    let matchName = unifiesTIdentifier l n (templateIdentifier $ entryType e')
    let proof = case ret of
                Nothing -> coercesList l args targs
                Just r -> do
                    coercesList l args (init targs)
                    tcCstrM_ l $ Unifies r (last targs)
    ok <- proveWith l (matchName >> proof)
    case ok of
        Left err -> return $ Left (e',err)
        Right ((),subst) -> do
            --ss <- liftM ppSubstsGeneric getSubstsGeneric
            --liftIO $ putStrLn $ "instantiated " ++ ppr n ++ " " ++ ppr args ++ " " ++ ppr ret ++ " " ++ ppr (entryType e') ++ "\n" ++ show ss ++  "INST\n" ++ ppr (tSubsts subst) ++ ppr (tValues subst)
            return $ Right (e',subst)

templateIdentifier :: Type -> TIdentifier
templateIdentifier (DecT t) = templateIdentifier' t
    where
    templateIdentifier' :: DecType -> TIdentifier
    templateIdentifier' (TpltType _ _ _ _ t) = templateIdentifier' t
    templateIdentifier' (ProcType _ _ n _ _ _) = Right n
    templateIdentifier' (StructType _ _ n _) = Left n
        
-- | Extracts a head signature from a template type declaration
templateArgs :: Location loc => TIdentifier -> EntryEnv loc -> TcM loc [Type]
templateArgs (Left name) e = case entryType e of
    DecT (TpltType _ args cstrs [] body) -> return $ map varNameToType args -- a base template uses the base arguments
    DecT (TpltType _ args cstrs specials body) -> return specials -- a specialization uses the specialized arguments
templateArgs (Right name) e = case entryType e of
    DecT (TpltType _ args cstrs [] (ProcType _ _ n vars ret stmts)) -> do -- include the return type
        return $ map (\(VarName t n) -> t) vars ++ [ret]
    DecT (ProcType _ _ n vars ret stmts) -> do -- include the return type
        return $ map (\(VarName t n) -> t) vars ++ [ret]
    otherwise -> genericError (locpos $ entryLoc e) $ text "Invalid type for procedure template"

-- | renames the variables in a template to local names
localTemplate :: (VarsTcM loc,Location loc) => EntryEnv loc -> TcM loc (EntryEnv loc)
localTemplate (e::EntryEnv loc) = case entryType e of
    DecT (TpltType tpltid args cstrs specials body) -> do
        uniqs <- mapM uniqueVar args
        -- VarName VarIdentifier () --> SecType
        let subt11 = substsFromList $ secs uniqs
        -- VarName VarIdentifier () --> BaseType
        let subt12 = substsFromList $ types uniqs
        -- TypeName VarIdentifier () --> TypeName VarIdentifier (Typed loc)
        let subt13 = substsFromList $ typeNames uniqs
        -- TypeName VarIdentifier () --> TypeName VarIdentifier ()
        let subt14 = substsFromList $ map (\(x,TypeName _ n) -> (x,TypeName () n)) $ typeNames uniqs
        -- TypeName VarIdentifier () --> TypeName VarIdentifier Type
        let subt15 = substsFromList $ map (\(x,TypeName t n) -> (x,TypeName (typed t) n)) $ typeNames uniqs
        -- VarName VarIdentifier () --> Expression VarIdentifier Type
        let subt2 = substsFromList $ map (\(x,y) -> (x,RVariablePExpr (loc y) y)) uniqs
        -- VarName VarIdentifier () --> Expression VarIdentifier (Typed loc)
        let subt3 = substsFromList $ map (\(x,y) -> (x,fmap (Typed l) $ RVariablePExpr (loc y) y)) uniqs
        -- VarName VarIdentifier () --> VarName VarIdentifier Type
        let subt4 = substsFromList uniqs
        let sub :: Vars (TcM loc) a => a -> TcM loc a
            sub = subst subt11 >=> subst subt12 >=> subst subt13 >=> subst subt14 >=> subst subt15 >=> subst subt2 >=> subst subt3 >=> subst subt4
        body' <- sub body
        cstrs' <- sub cstrs
        specials' <- sub specials
        let t' = DecT $ TpltType tpltid (map snd uniqs) cstrs' specials' body'
        v' <- sub (entryValue e)
        return $ EntryEnv l t' v'
    DecT t -> return e
  where
    uniqueVar :: VarName VarIdentifier Type -> TcM loc (VarName VarIdentifier (),VarName VarIdentifier Type)
    uniqueVar i@(VarName t v) = newTyVarId >>= \j -> return (VarName () v,VarName t (VarIdentifier (varIdBase v) $ Just j))
    l = entryLoc e
    secs :: [(a,VarName VarIdentifier Type)] -> [(a,SecType)]
    secs [] = []
    secs ((x,VarName (SType k) n):xs) = (x,SVar (VarName () n) k) : secs xs
    secs ((x,_):xs) = secs xs
    types :: [(a,VarName VarIdentifier Type)] -> [(a,BaseType)]
    types [] = []
    types ((x,VarName BType n):xs) = (x,BVar (VarName () n)) : types xs
    types ((x,_):xs) = types xs
    typeNames :: [(VarName VarIdentifier (),VarName VarIdentifier Type)] -> [(TypeName VarIdentifier (),TypeName VarIdentifier (Typed loc))]
    typeNames [] = []
    typeNames ((VarName () v,y@(VarName BType n)):xs) = (TypeName () v,TypeName (Typed l $ varNameToType y) n) : typeNames xs
    typeNames ((x,_):xs) = typeNames xs
    









