{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable, TypeFamilies, FlexibleContexts, DeriveGeneric #-}

module Language.SecreC.Error where

import Language.SecreC.Position
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.Location

import Data.Generics hiding (empty,Generic)
import Data.Int
import Data.Word
import Data.Hashable
import Data.Binary

import GHC.Generics (Generic)

import Control.Monad.Except
import Control.Monad.Writer (tell,MonadWriter(..))

import Text.Parsec (ParseError(..))
import Text.PrettyPrint as PP

data ParserException 
    = LexicalException String
    | ParsecException String 
    | DerpException String
    | PreProcessorException String
    deriving (Show,Typeable,Data,Eq,Ord,Generic)

instance Binary ParserException
instance Hashable ParserException

instance Monad m => PP m ParserException where
    pp (LexicalException s) = return $ text "Lexical error:" <+> text s
    pp (ParsecException err) = return $ text "Parser error:" <+> text err
    pp (DerpException msg) = return $ text "Parser error:" <+> text msg
    pp (PreProcessorException msg) = return $ text "Preprocessor error:" <+> text msg

parserError :: ParserException -> SecrecError
parserError = ParserError

data SecrecError = TypecheckerError Position TypecheckerErr
                 | ParserError ParserException
                 | ModuleError Position ModuleErr
                 | GenericError
                     Position -- ^ position
                     Doc -- ^message
                     (Maybe SecrecError) -- recursive error
                 | MultipleErrors [SecrecError] -- a list of errors
                 | TimedOut Int -- timed out after @x@ seconds
                 | OrWarn -- ^ optional constraint, just throw a warning
                     SecrecError
                 | ErrToken -- for internal purposes
  deriving (Show,Typeable,Data,Eq,Ord,Generic)
  
instance Binary SecrecError
instance Hashable SecrecError

instance Located SecrecError where
     type LocOf SecrecError = Position
     loc (TypecheckerError p _) = p
     loc (ParserError _) = noloc
     loc (ModuleError p _) = p
     loc (GenericError p _ _) = p
     loc (MultipleErrors es) = minimum (map loc es)
     loc (TimedOut _) = noloc
     loc (OrWarn e) = loc e
     loc (ErrToken) = noloc
     updLoc = error "cannot update location in errors"

instance Monad m => PP m SecrecError where
    pp (TypecheckerError p err) = do
        ppp <- pp p
        ppe <- pp err
        return $ ppp <> char ':' $+$ nest 4 ppe
    pp (ParserError err) = pp err
    pp (ModuleError p err) = do
        pp1 <- pp p
        pp2 <- pp err
        return $ pp1 <> char ':' $+$ nest 4 pp2
    pp (GenericError p msg Nothing) = do
        pp1 <- pp p
        return $ pp1 <> char ':' $+$ nest 4 msg
    pp (GenericError p msg (Just err)) = do
        pp1 <- pp p
        pp2 <- pp err
        return $ pp1 <> char ':' $+$ nest 4 msg $+$ text "Because of:" <+> pp2
    pp (MultipleErrors errs) = liftM vcat $ mapM pp errs
    pp (TimedOut i) = do
        ppi <- pp i
        return $ text "Computation timed out after" <+> ppi <+> text "seconds"
    pp (OrWarn err) = liftM (text "Warning: " <+>) (pp err)
    pp (ErrToken) = return $ text "<error>"

data TypecheckerErr
    = UnreachableDeadCode
        Doc -- unreachable statements
    | GenTcError -- generic typechecker error
        Doc -- message
        (Maybe SecrecError)
    | Halt -- ^ an error because of lacking information
        TypecheckerErr
    | NonStaticDimension -- ^ array dimension is not known statically
        Doc -- ^ array type
        SecrecError -- ^ sub-error
    | MismatchingArrayDimension -- ^ array dimension does not match sizes
        Doc -- type
        Doc -- expected dimension
        (Maybe SecrecError)
    | MultipleDefinedVariable Identifier
    | NoReturnStatement
        Doc -- declaration
        (Maybe SecrecError)
    | NoTemplateType
        Doc -- template name
        Position -- entry location
        Doc -- entry type
    | NoMatchingTemplateOrProcedure -- ^ suitable template instantiation not found
        Doc -- ^ expected match
        [(Position,Doc,SecrecError)] -- ^ declared instantiations in scope
    | NotDefinedDomain Doc
    | NotDefinedKind Doc
    | InvalidDomainVariableName -- ^ a domain already exists with the declared domain variable name
        Doc -- ^ variable name
        Position -- ^ domain declaration
    | InvalidKindVariableName -- ^ a kind already exists with the declared kind variable name
        Doc -- ^ variable name
        Position -- ^ domain declaration
    | InvalidTypeVariableName -- ^ a type already exists with the declared type variable name
        Doc -- ^ variable name
        [Position] -- ^ type declarations
    | MultipleDefinedKind
        Doc -- ^ kind name
        Position -- ^ position of the existing kind definition
    | NotDefinedType -- ^ type not found
        Doc -- ^ type name
    | NotDefinedProcedure -- ^ procedure not found
        Doc -- ^ procedure name
    | NotDefinedOperator -- ^ operator not found
        Doc -- ^ operator name
    | NoNonTemplateType -- ^ found a template type instead of a regular type
        Doc -- ^ type name
    | MultipleDefinedDomain -- ^ a newly-declared domain already exists
        Doc -- ^ domain name
        Position -- ^ Previous definition
    | MultipleDefinedField -- ^ a struct's field name is multiply defined
        Identifier -- ^ field name
        Position -- ^ previous definition
    | AmbiguousName -- ^ the same name refers to different entities
        Doc -- ^ name
        [Position] -- ^ different declarations
    | MultipleDefinedStructTemplate -- ^ overloaded template structs not supported
        Doc -- ^ template name
        Position -- ^ position of the already defined struct
    | EqualityException -- ^ @equals@ fails to prove equality
        String -- label
        Doc Doc -- types
        (Maybe SecrecError) -- sub-error
    | CoercionException -- ^ @coerces@ fails to prove equality
        String --label
        Doc Doc -- types
        (Maybe SecrecError) -- sub-error
    | NCoercionException -- ^ @coerces@ fails to prove equality
        String -- label
        (Maybe Doc) [Doc]
        (Maybe SecrecError) -- sub-error
    | UnificationException -- ^ @unifies@ fails to unify two types
        String -- label
        Doc Doc -- types
        (Maybe SecrecError) --  sub-error
    | ComparisonException -- ^ @compares@ fails to compare two types
        String -- label
        Doc Doc -- types
        (Maybe SecrecError) -- sub-error
    | MultipleDefinedStruct -- ^ a struct is multiply defined
        Doc -- ^struct name
        Position -- ^existing definition
    | NonDeclassifiableExpression -- ^ an expression cannot be declassified
    | FieldNotFound -- ^ field not found in structure definition
        Doc -- ^ type 
        Doc -- ^ field name
    | ArrayAccessOutOfBounds
        Doc -- type
        Word64 -- dimension
        Doc -- selection range
    | VariableNotFound -- variable not found in scope
        Doc -- ^ variable name
    | InvalidToStringArgument
    | InvalidSizeArgument
    | DuplicateTemplateInstances
        Doc -- expected match
        [(Position,Doc)] -- duplicate declarations
    | ConflictingTemplateInstances
        Doc -- expected match
        [(Position,Doc)] -- duplicate declarations
        SecrecError -- sub-error
    | TemplateSolvingError -- error solving a template constraint
        Doc -- template application
        SecrecError -- sub-error
    | StaticEvalError
        Doc -- expression
        (Maybe SecrecError) -- sub-error
    | UnresolvedVariable
        Doc -- variable name
    | MismatchingVariableType
        Doc -- variable
        SecrecError -- sub-error
    | UnresolvedMatrixProjection
        Doc -- ^ type
        Doc -- ^ ranges
        SecrecError -- ^ sub-error
    | UnresolvedFieldProjection
        Doc -- ^ type
        Doc -- ^ attribute
        SecrecError -- ^ sub-error
    | MultipleTypeSubstitutions -- a variable can be resolved in multiple ways
        [(Doc,SecrecError)] -- list of different substitution options
    | ConstraintStackSizeExceeded
        Doc -- limit
    | TypeConversionError
        Doc -- conversion kind
        Doc -- type to convert
    | NonPositiveIndexExpr
        Doc -- the index expression
        SecrecError -- sub-error
    | UncheckedRangeSelection -- dependent size in selection
        Doc -- type
        Word64 -- dimension where the dependent size occurs
        Doc -- range selection
        SecrecError -- ^ sub-error
    | StaticAssertionFailure
        Doc -- assertion
        SecrecError -- ^ sub-error
    | NotSupportedIndexOp -- failed to convert expression into IExpr or ICond
        Doc -- expression
        (Maybe SecrecError) -- sub-error
    | SMTException
        Doc -- hypotheses
        Doc -- expression
        SecrecError -- sub-error
    | FailAddHypothesis -- failed to add hypothesis
        Doc -- hypothesis
        SecrecError -- sub-error
    | AssignConstVariable
        Doc -- variable name
    | DependencyErr
        SecrecError -- dependency error
    | IndexConditionNotValid -- failed to prove mandatory index condition
        Doc -- condition
        SecrecError -- sub-error
  deriving (Show,Typeable,Data,Eq,Ord,Generic)

instance Binary TypecheckerErr
instance Hashable TypecheckerErr

instance Monad m => PP m TypecheckerErr where
    pp (GenTcError doc Nothing) = return doc
    pp (GenTcError doc (Just err)) = do
        ppe <- pp err
        return $ doc $+$ nest 4 (text "Because of:" <+> ppe)
    pp (Halt err) = do
        ppe <- pp err
        return $ text "Insufficient context to resolve constraint:" $+$ nest 4 ppe
    pp (IndexConditionNotValid c err) = do
        ppe <- pp err
        return $ text "Failed to satisfy index condition:" $+$ nest 4
            (text "Index condition:" <+> c
            $+$ text "Because of:" <+> ppe)
    pp (DependencyErr c) = do
        ppc <- pp c
        return $ text "Failed to solve constraint dependency:" $+$ nest 4 ppc
    pp (AssignConstVariable n) = do
        ppn <- pp n
        return $ text "Cannot perform assignment on constant variable" <+> quotes ppn
    pp (FailAddHypothesis hyp err) = do
        ppe <- pp err
        return $ text "Failed to add hypothesis" <+> quotes hyp $+$ nest 4
            (text "Because of:" $+$ (nest 4 ppe))
    pp (SMTException hyp prop err) = do
        ppe <- pp err
        return $ text "Failed to prove proposition via SMT solvers:" $+$ nest 4
            (text "Hypothesis:" $+$ (nest 4 hyp)
            $+$ text "Proposition:" $+$ (nest 4 prop)
            $+$ text "Because of:" $+$ (nest 4 ppe))        
    pp (NotSupportedIndexOp e Nothing) = return $ text "Failed to convert expression" <+> quotes e <+> text "into an index operation"
    pp (NotSupportedIndexOp e (Just err)) = do
        ppe <- pp err
        return $ text "Failed to convert expression" <+> quotes e <+> text "into an index operation" $+$ nest 4
            (text "Because of:" $+$ nest 4 ppe)
    pp (StaticAssertionFailure e err) = do
        ppe <- pp err
        return $ text "Failed to statically check assertion" <+> quotes e $+$ nest 4 (text "Because of:" $+$ nest 4 ppe)
    pp (NonPositiveIndexExpr e err) = do
        ppe <- pp err
        return $ text "Failed to prove that index expression" <+> quotes e <+> text ">= 0" $+$ nest 4 (text "Because of:" $+$ nest 4 ppe)
    pp (TypeConversionError k t) = return $ text "Expected a" <+> k <+> text "but found" <+> quotes t
    pp e@(UnreachableDeadCode {}) = return $ text (show e)
    pp e@(NonStaticDimension t err) = do
        ppe <- pp err
        return $ text "Array dimension must be statically known for type" <+> quotes t $+$ nest 4
            (text "Static evaluation error:" $+$ nest 4 ppe)
    pp e@(MismatchingArrayDimension t d Nothing) = return $ text "Expecting dimension" <+> d <+> text "for type" <+> quotes t
    pp e@(MismatchingArrayDimension t d (Just err)) = do
        ppe <- pp err
        return $ text "Expecting dimension" <+> d <+> text "for type" <+> quotes t <> char ':' $+$ nest 4 (text "Because of:" $+$ nest 4 ppe)
    pp e@(MultipleDefinedVariable {}) = return $ text (show e)
    pp e@(NoReturnStatement dec Nothing) = return $ text "No return statement in procedure or operator declaration:" $+$ nest 4 dec
    pp e@(NoReturnStatement dec (Just err)) = do
         ppe <- pp err
         return $ text "No return statement in procedure or operator declaration:" $+$ nest 4 (dec $+$ (text "Because of:" $+$ nest 4 ppe))
    pp e@(NoTemplateType n p t) = do
        ppp <- pp p
        return $ text "Declaration" <+> quotes t <+> text "at" <+> ppp <+> text "is not a template type with name" <+> quotes n
    pp e@(NoMatchingTemplateOrProcedure ex defs) = do
        let f1 (p,d,err) = do
            ppp <- pp p
            ppe <- pp err
            return $ ppp <> char ':' $+$ nest 4 ((text "Declaration:" $+$ nest 4 d) $+$ (text "Instantiation error:" $+$ nest 4 ppe))
        pp1 <- mapM f1 defs
        return $ text "Could not find matching template or procedure:" $+$ nest 4
               (text "Expected match:" <+> ex
            $+$ text "Actual declarations: " $+$ nest 4 (vcat pp1))
    pp e@(NotDefinedDomain {}) = return $ text (show e)
    pp e@(NotDefinedKind {}) = return $ text (show e)
    pp e@(InvalidDomainVariableName {}) = return $ text (show e)
    pp e@(InvalidKindVariableName {}) = return $ text (show e)
    pp e@(InvalidTypeVariableName {}) = return $ text (show e)
    pp e@(MultipleDefinedKind {}) = return $ text (show e)
    pp e@(NotDefinedType n) = return $ text "Could not find definition for type" <+> quotes n
    pp e@(NotDefinedProcedure n) = return $ text "Could not find definition for procedure" <+> quotes n
    pp e@(NotDefinedOperator o) = return $ text "Could not find definition for operator" <+> quotes (o)
    pp e@(NoNonTemplateType {}) = return $ text (show e)
    pp e@(MultipleDefinedDomain {}) = return $ text (show e)
    pp e@(MultipleDefinedField {}) = return $ text (show e)
    pp e@(AmbiguousName {}) = return $ text (show e)
    pp e@(MismatchingVariableType v err) = do
        ppe <- pp err
        return $ text "Type of variable" <+> quotes v <+> text "does not match expected type" $+$ nest 4 (text "Sub-error:" <+> ppe)
    pp e@(MultipleDefinedStructTemplate i p) = return $ text (show e)
    pp e@(EqualityException i t1 t2 env) = do
        ppe <- ppConstraintEnv env
        return $ text "Failed to prove" <+> text i <+> text "equality:" $+$ nest 4
               (text "Left:" <+> t1
            $+$ text "Right:" <+> t2
            $+$ ppe)
    pp e@(CoercionException i t1 t2 env) = do
        ppe <- ppConstraintEnv env
        return $ text "Failed to apply implicit" <+> text i <+> text "coercion:" $+$ nest 4
               (text "From:" <+> t1
            $+$ text "To:" <+> t2
            $+$ ppe)
    pp e@(NCoercionException i Nothing ts env) = do
        let f1 (i,t) = do
            ppi <- pp i
            ppt <- pp t
            return $ text "Direction" <+> ppi <> char ':' <+> ppt
        pp1 <- mapM f1 $ zip [(1::Int)..] ts
        ppe <- ppConstraintEnv env
        return $ text "Failed to apply multidirectional" <+> text i <+> text "coercion:" $+$ nest 4
               (vcat pp1 $+$ ppe)
    pp e@(NCoercionException i (Just t3) ts env) = do
        let f1 (i,t) = do
            ppi <- pp i
            ppt <- pp t
            return $ text "Direction" <+> ppi <> char ':' <+> ppt
        pp1 <- mapM f1 $ zip [(1::Int)..] ts
        ppe <- ppConstraintEnv env
        return $ text "Failed to apply multidirectional" <+> text i <+> text "coercion:" $+$ nest 4
               (vcat pp1
            $+$ text "Result:" <+> t3
            $+$ ppe)
    pp e@(UnificationException i t1 t2 env) = do
        ppe <- ppConstraintEnv env
        return $ text "Failed to unify " <+> text i <+> text ":" $+$ nest 4
               (text "Left:" <+> t1
            $+$ text "Right:" <+> t2
            $+$ ppe)
    pp e@(ComparisonException i t1 t2 env) = do
        ppe <- ppConstraintEnv env
        return $ text "Failed to compare" <+> text i <+> text ":" $+$ nest 4
               (text "Left:" <+> t1
            $+$ text "Right:" <+> t2
            $+$ ppe)
    pp e@(MultipleDefinedStruct {}) = return $ text (show e)
    pp e@(NonDeclassifiableExpression {}) = return $ text (show e)
    pp e@(FieldNotFound t a) = return $ text "Type" <+> quotes t <+> text "does not possess a field" <+> quotes a
    pp e@(ArrayAccessOutOfBounds t i rng) = return $ text "Range selection" <+> rng <+> text "of the" <+> ppOrdinal i <+> text "dimension of type" <+> quotes t <+> text "out of bounds"
    pp e@(VariableNotFound v) = return $ text "Variable" <+> quotes v <+> text "not found"
    pp e@(InvalidToStringArgument {}) = return $ text (show e)
    pp e@(InvalidSizeArgument {}) = return $ text (show e)
    pp e@(DuplicateTemplateInstances ex defs) = do
        let f1 (p,d) = do
            ppp <- pp p
            return $ ppp <> char ':' $+$ nest 4 d
        pp1 <- mapM f1 defs
        return $ text "Duplicate matching instances for template or procedure application:" $+$ nest 4
               (text "Expected match:" <+> ex
            $+$ text "Duplicate declarations: " $+$ nest 4 (vcat pp1))
    pp e@(ConflictingTemplateInstances ex defs err) = do
        let f1 (p,d) = do
            ppp <- pp p
            return $ ppp <> char ':' $+$ nest 4 d
        pp1 <- mapM f1 defs
        ppe <- pp err
        return $ text "Conflicting matching instances for template or procedure application:" $+$ nest 4
               (text "Expected match:" <+> ex
            $+$ text "Conflicting declarations: " $+$ nest 4 (vcat pp1)
            $+$ text "Conflict: " $+$ nest 4 ppe)
    pp (TemplateSolvingError app err) = do
        ppe <- pp err
        return $ text "Failed to solve template instantiation:" <+> app $+$ nest 4 (text "Because of:" $+$ nest 4 ppe)
    pp (StaticEvalError e env) = do
        ppe <- ppConstraintEnv env
        return $ text "Unable to statically evaluate" <+> quotes e <> char ':' $+$ nest 4 ppe
    pp (UnresolvedVariable v) = return $ text "Unable to resolve variable: " <+> quotes v
    pp (UnresolvedMatrixProjection t rngs err) = do
        ppe <- pp err
        return $ text "Unable to resolve matrix projection:" $+$ nest 4 ((text "Type:" <+> t <> rngs) $+$ (text "Error:" $+$ nest 4 ppe))
    pp (UnresolvedFieldProjection t att err) = do
        ppe <- pp err
        return $ text "Unable to resolve struct field:" $+$ nest 4 ((text "Type:" <+> t <> char '.' <> att) $+$ (text "Error:" $+$ nest 4 ppe))
    pp (MultipleTypeSubstitutions opts) = do
        let f (i,(bind,ss)) = do
            pps <- pp ss
            return $ text "Option" <+> integer i <> char ':' <+> bind $+$ nest 4 pps
        pp1 <- mapM f $ zip [1..] opts
        return $ text "Multiple type substitutions:" $+$ nest 4 (vcat pp1)
    pp (ConstraintStackSizeExceeded i) = return $ text "Exceeded constraint stack size of" <+> quotes i
    pp w@(UncheckedRangeSelection t i rng err) = do
        pperr <- pp err
        return $ text "Range selection" <+> rng <+> text "of the" <+> ppOrdinal i <+> text "dimension can not be checked for type" <+> quotes t $+$ nest 4 (text "Because of:" <+> pperr)
    

ppConstraintEnv Nothing = return PP.empty
ppConstraintEnv (Just suberr) = do
    pp1 <- pp suberr
    return $ text "Because of:" $+$ nest 4 pp1

isHaltError :: SecrecError -> Bool
isHaltError = everything (||) (mkQ False aux)
    where
    aux :: TypecheckerErr -> Bool
    aux (Halt vs) = True
    aux _ = False

isOrWarnError :: SecrecError -> Bool
isOrWarnError = everything (||) (mkQ False aux)
    where
    aux :: SecrecError -> Bool
    aux (OrWarn _) = True
    aux _ = False

data ModuleErr
    = DuplicateModuleName Identifier FilePath FilePath
    | ModuleNotFound Identifier
    | CircularModuleDependency [(Identifier,Identifier,Position)]
  deriving (Show,Read,Data,Typeable,Eq,Ord,Generic)

instance Binary ModuleErr
instance Hashable ModuleErr

instance Monad m => PP m ModuleErr where
    pp (DuplicateModuleName i f1 f2) = return $ text "Duplicate module" <+> quotes (text i) <> char ':' $+$ nest 4 (text f1 $+$ text f2)
    pp (ModuleNotFound i) = return $ text "Module" <+> quotes (text i) <+> text "not found"
    pp (CircularModuleDependency g) = do
        pp1 <- mapM ppNode g
        return $ text "Circular module dependency:" $+$ nest 4 (vcat pp1)
      where
        ppNode (from,to,l) = do
            ppl <- pp l
            return $ quotes (text from) <+> text "imports" <+> quotes (text to) <+> text "at" <+> ppl

moduleError :: Position -> ModuleErr -> SecrecError
moduleError = ModuleError

modError :: MonadError SecrecError m => Position -> ModuleErr -> m a
modError pos msg = throwError $ moduleError pos msg

genError :: MonadError SecrecError m => Position -> Doc -> m a
genError pos msg = throwError $ GenericError pos msg Nothing

typecheckerError :: Position -> TypecheckerErr -> SecrecError
typecheckerError = TypecheckerError

data SecrecWarning
    = TypecheckerWarning Position TypecheckerWarn
    | ErrWarn SecrecError
  deriving (Show,Typeable,Eq,Ord,Generic)

instance Binary SecrecWarning
instance Hashable SecrecWarning

instance Located SecrecWarning where
    type LocOf SecrecWarning = Position
    loc (TypecheckerWarning p _) = p
    loc (ErrWarn e) = loc e
    updLoc = error "no updLoc for errors"

instance Monad m => PP m SecrecWarning where
    pp (TypecheckerWarning p w) = do
        ppp <- pp p
        ppw <- pp w
        return $ text "Warning:" <+> ppp $+$ nest 4 ppw
    pp (ErrWarn err) = liftM (text "Warning:" <+>) (pp err)
  
data TypecheckerWarn
    = UnusedVariable
        Doc -- ^ variable
--    | DependentSizeSelection -- dependent size in selection
--        Doc -- type
--        Word64 -- dimension where the dependent size occurs
--        (Maybe Doc) -- range selection
--        SecrecError -- ^ sub-error
--    | DependentMatrixSize
--        Doc -- type
--        Word64 -- size's dimension
--        Doc -- dependent expression
--        (Maybe Doc) -- variable declaration
--        SecrecError -- ^ sub-error
--    | DependentMatrixDimension
--        Doc -- partial type
--        Doc -- dependent expression
--        (Maybe Doc) -- variable declaration
--        SecrecError -- ^ sub-error
    | EmptyBranch
        Doc -- statement
    | SingleIterationLoop
        Doc -- statement
    | ShadowedVariable
        Doc -- ^ name of the shadowed variable
        Position -- ^ shadowed position
    | LiteralOutOfRange -- literal out of range
        String -- literal value
        Doc -- type
        String -- min range
        String -- max range
  deriving (Data,Show,Typeable,Eq,Ord,Generic)

instance Binary TypecheckerWarn 
instance Hashable TypecheckerWarn

instance Monad m => PP m TypecheckerWarn where
    pp w@(UnusedVariable v) = return $ text "Unused variable" <+> quotes v
    pp w@(EmptyBranch s) = return $ text "Conditional branch statement is empty:" $+$ s
    pp w@(SingleIterationLoop s) = return $ text "Single iteration loop with body:" $+$ s
    pp w@(ShadowedVariable n p) = do
        ppp <- pp p
        return $ text "Variable" <+> quotes n <+> text "shadows definition from" <+> ppp
    pp w@(LiteralOutOfRange lit ty min max) = return $ text "Literal" <+> quotes (text lit) <+> text "out of the range" <+> brackets (text min <> text ".." <> text max) <+> text "for type" <+> quotes ty
