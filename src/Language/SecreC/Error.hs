{-# LANGUAGE DeriveDataTypeable, TypeFamilies, FlexibleContexts #-}

module Language.SecreC.Error where

import Language.SecreC.Position
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.Location

import Data.Generics hiding (empty)
import Data.Int
import Data.Word

import Control.Monad.Except
import Control.Monad.Writer (tell,MonadWriter(..))

import Text.Parsec (ParseError(..))
import Text.PrettyPrint as PP

data ParserException 
    = LexicalException String
    | ParsecException String 
    | DerpException String
    deriving (Show,Typeable,Data,Eq,Ord)

instance PP ParserException where
    pp (LexicalException s) = text "Lexical error:" <+> text s
    pp (ParsecException err) = text "Parser error:" <+> text err
    pp (DerpException msg) = text "Parser error:" <+> text msg

parserError :: ParserException -> SecrecError
parserError = ParserError

data SecrecError = TypecheckerError Position TypecheckerErr
                 | ParserError ParserException
                 | ModuleError Position ModuleErr
                 | GenericError
                     Position -- ^ position
                     Doc -- ^message
                 | MultipleErrors [SecrecError] -- a list of errors
                 | TimedOut Int -- timed out after @x@ seconds
                 | OrWarn -- ^ optional constraint, just throw a warning
                     SecrecError
                | Halt -- ^ an error because of lacking information
                    SecrecError
  deriving (Show,Typeable,Data,Eq,Ord)

instance Located SecrecError where
     type LocOf SecrecError = Position
     loc (TypecheckerError p _) = p
     loc (ParserError _) = noloc
     loc (ModuleError p _) = p
     loc (GenericError p _) = p
     loc (MultipleErrors es) = minimum (map loc es)
     loc (TimedOut _) = noloc
     loc (OrWarn e) = loc e
     loc (Halt e) = loc e
     updLoc = error "cannot update location in errors"

instance PP SecrecError where
    pp (TypecheckerError p err) = pp p <> char ':' $+$ nest 4 (pp err)
    pp (ParserError err) = pp err
    pp (ModuleError p err) = pp p <> char ':' $+$ nest 4 (pp err)
    pp (GenericError p msg) = pp p <> char ':' $+$ nest 4 msg
    pp (MultipleErrors errs) = vcat $ map pp errs
    pp (TimedOut i) = text "Computation timed out after" <+> pp i <+> text "seconds"
    pp (OrWarn err) = pp err
    pp (Halt err) = text "Insufficient context to resolve constraint:" $+$ nest 4 (pp err)

data TypecheckerErr
    = UnreachableDeadCode
        Doc -- unreachable statements
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
    | BiCoercionException -- ^ @coerces@ fails to prove equality
        String -- label
        (Maybe Doc) Doc Doc -- types
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
        [Doc] -- list of different substitution options
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
  deriving (Show,Typeable,Data,Eq,Ord)

instance PP TypecheckerErr where
    pp (IndexConditionNotValid c err) = text "Failed to satisfy index condition:" $+$ nest 4
        (text "Index condition:" <+> c
        $+$ text "Because of:" <+> pp err)
    pp (DependencyErr c) = text "Failed to solve constraint dependency:" $+$ nest 4 (pp c)
    pp (AssignConstVariable n) = text "Cannot perform assignment on constant variable" <+> quotes (pp n)
    pp (FailAddHypothesis hyp err) = text "Failed to add hypothesis" <+> quotes hyp $+$ nest 4
        (text "Because of:" $+$ (nest 4 (pp err)))
    pp (SMTException hyp prop err) = text "Failed to prove proposition via SMT solvers:" $+$ nest 4
        (text "Hypothesis:" $+$ (nest 4 hyp)
        $+$ text "Proposition:" $+$ (nest 4 prop)
        $+$ text "Because of:" $+$ (nest 4 (pp err)))        
    pp (NotSupportedIndexOp e Nothing) = text "Failed to convert expression" <+> quotes e <+> text "into an index operation"
    pp (NotSupportedIndexOp e (Just err)) = text "Failed to convert expression" <+> quotes e <+> text "into an index operation" $+$ nest 4
        (text "Because of:" $+$ nest 4 (pp err))
    pp (StaticAssertionFailure e err) = text "Failed to statically check assertion" <+> quotes e $+$ nest 4 (text "Because of:" $+$ nest 4 (pp err))
    pp (NonPositiveIndexExpr e err) = text "Failed to prove that index expression" <+> quotes e <+> text ">= 0" $+$ nest 4 (text "Because of:" $+$ nest 4 (pp err))
    pp (TypeConversionError k t) = text "Expected a" <+> k <+> text "but found" <+> quotes t
    pp e@(UnreachableDeadCode {}) = text (show e)
    pp e@(NonStaticDimension t err) = text "Array dimension must be statically known for type" <+> quotes t $+$ nest 4
        (text "Static evaluation error:" $+$ nest 4 (pp err))
    pp e@(MismatchingArrayDimension t d Nothing) = text "Expecting dimension" <+> d <+> text "for type" <+> quotes t
    pp e@(MismatchingArrayDimension t d (Just err)) = text "Expecting dimension" <+> d <+> text "for type" <+> quotes t <> char ':' $+$ nest 4 (text "Because of:" $+$ nest 4 (pp err))
    pp e@(MultipleDefinedVariable {}) = text (show e)
    pp e@(NoReturnStatement dec) = text "No return statement in procedure or operator declaration:" $+$ nest 4 dec
    pp e@(NoTemplateType n p t) = text "Declaration" <+> quotes t <+> text "at" <+> pp p <+> text "is not a template type with name" <+> quotes n
    pp e@(NoMatchingTemplateOrProcedure ex defs) = text "Could not find matching template or procedure:" $+$ nest 4
           (text "Expected match:" <+> ex
        $+$ text "Actual declarations: " $+$ nest 4 (vcat (map (\(p,d,err) -> pp p <> char ':' $+$ nest 4 ((text "Declaration:" $+$ nest 4 d) $+$ (text "Instantiation error:" $+$ nest 4 (pp err)))) defs))
        )
    pp e@(NotDefinedDomain {}) = text (show e)
    pp e@(NotDefinedKind {}) = text (show e)
    pp e@(InvalidDomainVariableName {}) = text (show e)
    pp e@(InvalidTypeVariableName {}) = text (show e)
    pp e@(MultipleDefinedKind {}) = text (show e)
    pp e@(NotDefinedType n) = text "Could not find definition for type" <+> quotes n
    pp e@(NotDefinedProcedure n) = text "Could not find definition for procedure" <+> quotes n
    pp e@(NotDefinedOperator o) = text "Could not find definition for operator" <+> quotes (o)
    pp e@(NoNonTemplateType {}) = text (show e)
    pp e@(MultipleDefinedDomain {}) = text (show e)
    pp e@(MultipleDefinedField {}) = text (show e)
    pp e@(AmbiguousName {}) = text (show e)
    pp e@(MismatchingVariableType v err) = text "Type of variable" <+> quotes v <+> text "does not match expected type" $+$ nest 4 (text "Sub-error:" <+> pp err)
    pp e@(MultipleDefinedStructTemplate i p) = text (show e)
--        text "Overloaded templates for struct" <+> quotes (text i) <+> text "not supported:"
--        $+$ nest 4 (error "TODO")
    pp e@(EqualityException i t1 t2 env) = text "Failed to prove" <+> text i <+> text "equality:" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(CoercionException i t1 t2 env) = text "Failed to apply implicit" <+> text i <+> text "coercion:" $+$ nest 4
           (text "From:" <+> t1
        $+$ text "To:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(BiCoercionException i Nothing t1 t2 env) = text "Failed to apply bidirectional" <+> text i <+> text "coercion:" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(BiCoercionException i (Just t3) t1 t2 env) = text "Failed to apply bidirectional" <+> text i <+> text "coercion:" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ text "Result:" <+> t3
        $+$ ppConstraintEnv env)
    pp e@(UnificationException i t1 t2 env) = text "Failed to unify " <+> text i <+> text ":" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(ComparisonException i t1 t2 env) = text "Failed to compare" <+> text i <+> text ":" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(MultipleDefinedStruct {}) = text (show e)
    pp e@(NonDeclassifiableExpression {}) = text (show e)
    pp e@(FieldNotFound t a) = text "Type" <+> quotes t <+> text "does not possess a field" <+> quotes a
    pp e@(ArrayAccessOutOfBounds t i rng) = text "Range selection" <+> rng <+> text "of the" <+> ppOrdinal i <+> text "dimension of type" <+> quotes t <+> text "out of bounds"
    pp e@(VariableNotFound v) = text "Variable" <+> quotes v <+> text "not found"
    pp e@(InvalidToStringArgument {}) = text (show e)
    pp e@(InvalidSizeArgument {}) = text (show e)
    pp e@(DuplicateTemplateInstances ex defs) = text "Duplicate matching instances for template or procedure application:" $+$ nest 4
           (text "Expected match:" <+> ex
        $+$ text "Duplicate declarations: " $+$ nest 4 (vcat (map (\(p,d) -> pp p <> char ':' $+$ nest 4 d) defs))
        )
    pp e@(ConflictingTemplateInstances ex defs err) = text "Conflicting matching instances for template or procedure application:" $+$ nest 4
           (text "Expected match:" <+> ex
        $+$ text "Conflicting declarations: " $+$ nest 4 (vcat (map (\(p,d) -> pp p <> char ':' $+$ nest 4 d) defs))
        $+$ text "Conflict: " $+$ nest 4 (pp err))
    pp (TemplateSolvingError app err) = text "Failed to solve template instantiation:" <+> app
        $+$ nest 4 (text "Because of:" $+$ nest 4 (pp err))
    pp (StaticEvalError e env) = text "Unable to statically evaluate" <+> quotes e <> char ':' $+$ nest 4 (ppConstraintEnv env)
    pp (UnresolvedVariable v) = text "Unable to resolve variable: " <+> quotes v
    pp (UnresolvedMatrixProjection t rngs err) = text "Unable to resolve matrix projection:" $+$ nest 4
        ((text "Type:" <+> t <> rngs) $+$ (text "Error:" $+$ nest 4 (pp err)))
    pp (UnresolvedFieldProjection t att err) = text "Unable to resolve struct field:" $+$ nest 4
        ((text "Type:" <+> t <> char '.' <> att) $+$ (text "Error:" $+$ nest 4 (pp err)))
    pp (MultipleTypeSubstitutions opts) = text "Multiple type substitutions:" $+$ nest 4 (vcat $ map f $ zip [1..] opts)
        where f (i,ss) = text "Option" <+> integer i <> char ':' $+$ nest 4 (pp ss)
    pp (ConstraintStackSizeExceeded i) = text "Exceeded constraint stack size of" <+> quotes i
    pp w@(UncheckedRangeSelection t i rng err) = text "Range selection" <+> rng <+> text "of the" <+> ppOrdinal i <+> text "dimension can not be checked for type" <+> quotes t $+$ nest 4
        (text "Because of:" <+> pp err)
    

ppConstraintEnv Nothing = PP.empty
ppConstraintEnv (Just suberr) = text "Because of:" $+$ nest 4 (pp suberr)

isHaltError :: SecrecError -> Bool
isHaltError = everything (||) (mkQ False aux)
    where
    aux :: SecrecError -> Bool
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
  deriving (Show,Read,Data,Typeable,Eq,Ord)

instance PP ModuleErr where
    pp (DuplicateModuleName i f1 f2) = text "Duplicate module" <+> quotes (text i) <> char ':' $+$ nest 4 (text f1 $+$ text f2)
    pp (ModuleNotFound i) = text "Module" <+> quotes (text i) <+> text "not found"
    pp (CircularModuleDependency g) = text "Circular module dependency:" $+$ nest 4 (vcat $ map ppNode g)
        where ppNode (from,to,l) = quotes (text from) <+> text "imports" <+> quotes (text to) <+> text "at" <+> pp l

moduleError :: Position -> ModuleErr -> SecrecError
moduleError = ModuleError

modError :: MonadError SecrecError m => Position -> ModuleErr -> m a
modError pos msg = throwError $ moduleError pos msg

genError :: MonadError SecrecError m => Position -> Doc -> m a
genError pos msg = throwError $ GenericError pos msg

typecheckerError :: Position -> TypecheckerErr -> SecrecError
typecheckerError = TypecheckerError

data SecrecWarning
    = TypecheckerWarning Position TypecheckerWarn
    | ErrWarn SecrecError
  deriving (Show,Typeable,Eq,Ord)

instance Located SecrecWarning where
    type LocOf SecrecWarning = Position
    loc (TypecheckerWarning p _) = p
    loc (ErrWarn e) = loc e
    updLoc = error "no updLoc for errors"

instance PP SecrecWarning where
    pp (TypecheckerWarning p w) = text "Warning:" <+> pp p $+$ nest 4 (pp w)
    pp (ErrWarn err) = text "Warning:" <+> pp err
  
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
  deriving (Data,Show,Typeable,Eq,Ord)

instance PP TypecheckerWarn where
    pp w@(UnusedVariable v) = text "Unused variable" <+> quotes v
--    pp w@(DependentSizeSelection t i Nothing err) = text "Array size of the" <+> ppOrdinal i <+> text "dimension is not statically know for type" <+> quotes t $+$ nest 4
--        (text "Static evaluation error:" <+> pp err)
--    pp w@(DependentSizeSelection t i (Just rng) err) = text "Range selection" <+> rng <+> text "of the" <+> ppOrdinal i <+> text "dimension is not statically know for type" <+> quotes t $+$ nest 4
--        (text "Static evaluation error:" <+> pp err)
--    pp w@(DependentMatrixSize t d e mb err) = text "Dependent array size" <+> quotes e <+> text "in the" <+> ppOrdinal d <+> text "dimension of type" <+> t <+> maybe empty (\v -> text "in the variable declaration of" <+> quotes v) mb $+$ nest 4
--        (text "Static evaluation error:" <+> pp err)
--    pp w@(DependentMatrixDimension t e mb err) = text "Dependent array dimension" <+> quotes e <+> text "for type" <+> t <+> maybe empty (\v -> text "in the variable declaration of" <+> quotes v) mb $+$ nest 4
--        (text "Static evaluation error:" <+> pp err)
    pp w@(EmptyBranch s) = text "Conditional branch statement is empty:" $+$ s
    pp w@(SingleIterationLoop s) = text "Single iteration loop with body:" $+$ s
    pp w@(ShadowedVariable n p) = text "Variable" <+> quotes n <+> text "shadows definition from" <+> pp p
    pp w@(LiteralOutOfRange lit ty min max) = text "Literal" <+> quotes (text lit) <+> text "out of the range" <+> brackets (text min <> text ".." <> text max) <+> text "for type" <+> quotes ty
