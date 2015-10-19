module Language.SecreC.TypeChecker.Type where

import Language.SecreC.Vars
import Language.SecreC.Utils
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Location
import Language.SecreC.Position
import Language.SecreC.Error
import Language.SecreC.TypeChecker.Base
import {-# SOURCE #-} Language.SecreC.TypeChecker.Expression

import Data.Traversable
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Map (Map(..))
import qualified Data.Map as Map
import Control.Monad hiding (mapM)
import Prelude hiding (mapM)

tcTypeSpec :: Location loc => TypeSpecifier loc -> TcM loc (TypeSpecifier (Typed loc))
tcTypeSpec (TypeSpecifier l sec dta dim) = do
    (sec',tsec) <- tcMbSecTypeSpec sec 
    dta' <- tcDatatypeSpec dta
    let tdta = typed $ loc dta'
    (dim',tdim) <- tcMbDimtypeSpec dim
    let t = CType tsec tdta tdim Nothing -- return type without array sizes
    return $ TypeSpecifier (Typed l t) sec' dta' dim'
    
tcMbSecTypeSpec :: Location loc => Maybe (SecTypeSpecifier loc) -> TcM loc (Maybe (SecTypeSpecifier (Typed loc)),Type)
tcMbSecTypeSpec Nothing = return (Nothing,Public) -- public by default
tcMbSecTypeSpec (Just sec) = do
    sec' <- tcSecTypeSpec sec
    let t = typed $ loc sec'
    return (Just sec',t)

tcSecTypeSpec :: Location loc => SecTypeSpecifier loc -> TcM loc (SecTypeSpecifier (Typed loc))
tcSecTypeSpec (PublicSpecifier l) = do
    return $ PublicSpecifier (Typed l Public)
tcSecTypeSpec (PrivateSpecifier l d) = do
    t <- checkPrivateDomain d
    let d' = fmap (flip Typed t) d
    return $ PrivateSpecifier (Typed l t) d'

tcDatatypeSpec :: Location loc => DatatypeSpecifier loc -> TcM loc (DatatypeSpecifier (Typed loc))
tcDatatypeSpec (PrimitiveSpecifier l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveSpecifier (Typed l t) p'
tcDatatypeSpec tplt@(TemplateSpecifier {}) = do
    b <- insideTemplate
    if b
        then tcTemplateTypeConstraint tplt
        else tcTemplateTypeResolve tplt 
tcDatatypeSpec (VariableSpecifier l v) = do
    t <- checkType v
    let v' = fmap (flip Typed t) v 
    return $ VariableSpecifier (Typed l t) v'

-- | Raises a template constraint
tcTemplateTypeConstraint :: Location loc => DatatypeSpecifier loc -> TcM loc (DatatypeSpecifier (Typed loc))
tcTemplateTypeConstraint (TemplateSpecifier l n@(TypeName tl tn) args) = do
    args' <- mapM tcTemplateTypeArgument args
    let t = TApp tn (map (typed . loc) args') emptyTDict
    let cstr = TCstr tn (map (typed . loc) args')
    let l' = Typed l t
    let n' = fmap notTyped n -- we dont't type the template name, only the application
    addTemplateConstraint cstr -- add constraint to the environment
    return $ TemplateSpecifier l' n' args'

-- | Resolves a template constraint by finding a best match among the template definitions in scope.
-- Best match here means the most specific constraint. If there is no best match, an error is raised.
-- argument types must be monomorphic
tcTemplateTypeResolve :: Location loc => DatatypeSpecifier loc -> TcM loc (DatatypeSpecifier (Typed loc))
tcTemplateTypeResolve (TemplateSpecifier l n@(TypeName tl tn) args) = do
    entries <- checkTemplateType n
    args' <- mapM tcTemplateTypeArgument args
    t <- matchTemplateType l n args' entries
    let l' = Typed l t
    let n' = fmap notTyped n -- we don't type the template name, only the application
    return $ TemplateSpecifier l' n' args'

-- | Matches a list of constraints and produces a dictionary as a witness
resolveTemplateTypeConstraints :: Location loc => [TCstr] -> TcM loc TDict
resolveTemplateTypeConstraints = undefined --foldM (\d c -> liftM (Map.union d) resolveTemplateTypeConstraint c) emptyTDict

-- | Matches a constraint and produces a dictionary as a witness
resolveTemplateTypeConstraint :: Location loc => TCstr -> TcM loc TDict
resolveTemplateTypeConstraint (TCstr tn args) = undefined
    
-- | Matches a list of monomorphically-typed template arguments against a list of template declarations
matchTemplateType :: Location loc => loc -> TypeName loc -> [TemplateTypeArgument (Typed loc)] -> [EntryEnv loc] -> TcM loc Type
matchTemplateType l n args es = do
    es' <- instantiateTemplateTypeEntries args es
    case es' of
        [] -> tcError (locpos l) $ NoMatchingTemplate (fmap locpos n) (map (fmap locpos) args) (map (locpos . entryLoc) es)
        es -> do
            -- sort the declarations from most to least specific: this will issue an error if two declarations are not comparable
            ((e,subst):_) <- tcReaderM $ sortByM (compareTemplateTypeDecls l $ typeId n) es
            -- return the instantiated body of the most specific declaration
            resolveTemplateTypeEntry e subst

resolveTemplateTypeEntry :: Location loc => EntryEnv loc -> Substs Type -> TcM loc Type
resolveTemplateTypeEntry e s = case entryType e of
    TpltType vars cstrs specials body -> do
        let cstrs' = substTraversable s cstrs -- specialize the constraints
        let specials' = substTraversable s specials -- specialize the specializations
        dict <- resolveTemplateTypeConstraints cstrs' -- compute a dictionary from the constraints
        let body' = subst s body -- specialize the struct's body
        let body'' = addTDict dict body' -- pass the dictionary to resolve inner template instantiations
        return body''

-- | Tells if one declaration is more specific than another, and if not it fails
compareTemplateTypeDecls :: Location loc => loc -> Identifier -> (EntryEnv loc,Substs Type) -> (EntryEnv loc,Substs Type) -> TcReaderM loc Ordering
compareTemplateTypeDecls l n (e1,s1) (e2,d2) = compares l (entryTypeHead n e1) (entryTypeHead n e2)
     
-- | Try to make each of the argument types an instance of each template declaration, and returns a substitution for successful ones.
-- Ignores templates with different number of arguments. 
-- Matching does not consider constraints.
instantiateTemplateTypeEntries :: [TemplateTypeArgument (Typed loc)] -> [EntryEnv loc] -> TcM loc [(EntryEnv loc,Substs Type)]
instantiateTemplateTypeEntries args es = undefined --foldM (\xs e -> xs ++ instantiateTemplateTypeEntry args e) [] es

instantiateTemplateTypeEntry :: [TemplateTypeArgument (Typed loc)] -> EntryEnv loc -> TcM loc [(EntryEnv loc,Substs Type)]
instantiateTemplateTypeEntry args e = undefined

tcPrimitiveDatatype :: Location loc => PrimitiveDatatype loc -> TcM loc (PrimitiveDatatype (Typed loc))
tcPrimitiveDatatype p = do
    let t = PrimType $ fmap (const ()) p
    let p' = fmap (flip Typed t) p
    return p'

tcTemplateTypeArgument :: Location loc => TemplateTypeArgument loc -> TcM loc (TemplateTypeArgument (Typed loc))
tcTemplateTypeArgument (GenericTemplateTypeArgument l n) = do
    t <- checkTemplateArg n
    let n' = fmap (flip Typed t) n
    return $ GenericTemplateTypeArgument (Typed l t) n'
tcTemplateTypeArgument (TemplateTemplateTypeArgument l n args) = do
    TemplateSpecifier l' n' args' <- tcDatatypeSpec (TemplateSpecifier l n args)
    return $ TemplateTemplateTypeArgument l' n' args'
tcTemplateTypeArgument (PrimitiveTemplateTypeArgument l p) = do
    p' <- tcPrimitiveDatatype p
    let t = typed $ loc p'
    return $ PrimitiveTemplateTypeArgument (Typed l t) p'
tcTemplateTypeArgument (IntTemplateTypeArgument l i) = do
    let t = TDim i
    return $ IntTemplateTypeArgument (Typed l t) i
tcTemplateTypeArgument (PublicTemplateTypeArgument l) = do
    let t = Public
    return $ PublicTemplateTypeArgument (Typed l t)

tcMbDimtypeSpec :: Location loc => Maybe (DimtypeSpecifier loc) -> TcM loc (Maybe (DimtypeSpecifier (Typed loc)),Expression ())
tcMbDimtypeSpec Nothing = return (Nothing,zeroExpr) -- 0 by default
tcMbDimtypeSpec (Just dim) = do
    (dim',t) <- tcDimtypeSpec dim
    return (Just dim',t)

tcDimtypeSpec :: Location loc => DimtypeSpecifier loc -> TcM loc (DimtypeSpecifier (Typed loc),Expression ())
tcDimtypeSpec (DimSpecifier l e) = do
    e' <- tcDimSizeExpr Nothing e
    return (DimSpecifier (notTyped l) e',fmap (const ()) e') 

tcRetTypeSpec :: Location loc => ReturnTypeSpecifier loc -> TcM loc (ReturnTypeSpecifier (Typed loc))
tcRetTypeSpec (ReturnType l Nothing) = do
    let t = Void
    return $ ReturnType (Typed l Void) Nothing
tcRetTypeSpec (ReturnType l (Just s)) = do
    s' <- tcTypeSpec s
    let t = typed $ loc s'
    return $ ReturnType (Typed l t) (Just s')

-- | Retrieves a constant dimension from a type
typeDim :: Location loc => loc -> Type -> TcReaderM loc Int
typeDim l (CType _ _ e _) = do
    let le = fmap (const noloc) e
    mb <- integerLitExpr le
    case mb of
        Nothing -> tcError (locpos l) $ NoStaticDimension (fmap locpos le)
        Just (_,i) -> return i
typeDim l _ = error "no dimension"



