{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

module Language.SecreC.Error where

import Language.SecreC.Position
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens
import Language.SecreC.Pretty
import Language.SecreC.Utils
import Language.SecreC.Vars

import Data.Generics hiding (empty)
import Data.Int
import Data.Word

import Control.Monad.Except
import Control.Monad.Writer (tell,MonadWriter(..))

import Text.Parsec (ParseError(..))
import Text.PrettyPrint

data ParserException 
    = LexicalException String
    | ParsecException ParseError 
    | DerpException String
    deriving (Show,Typeable,Data)

instance Data ParseError where
    gunfold = error "gunfold ParseError"
    toConstr = error "toConstr ParseError"
    dataTypeOf = error "dataTypeof ParseError"

instance PP ParserException where
    pp (LexicalException s) = text "Lexical error:" <+> text s
    pp (ParsecException err) = text "Parser error:" <+> text (show err)
    pp (DerpException msg) = text "Parser error:" <+> text msg

parserError :: ParserException -> SecrecError
parserError = ParserError

data SecrecError = TypecheckerError Position TypecheckerErr
                 | ParserError ParserException
                 | ModuleError Position ModuleErr
                 | GenericError
                     Position -- ^ position
                     Doc -- ^message
  deriving (Show,Typeable,Data)

instance PP SecrecError where
    pp (TypecheckerError p err) = pp p <> char ':' $+$ nest 4 (pp err)
    pp (ParserError err) = pp err
    pp (ModuleError p err) = pp p <> char ':' $+$ nest 4 (pp err)
    pp (GenericError p msg) = pp p <> char ':' $+$ nest 4 msg

data TypecheckerErr
    = UnreachableDeadCode
        Doc -- unreachable statements
    | NonStaticDimension -- ^ array dimension is not known statically
        Doc -- ^ array type
        SecrecError -- ^ sub-error
    | MismatchingArrayDimension -- ^ array dimension does not match sizes
        Doc -- type
        Word64 -- defined dimension
        Word64 -- expected dimension
        (Either Doc (Doc,Doc)) -- name of the array variable
    | MultipleDefinedVariable Identifier
    | NoReturnStatement
        Doc -- declaration
    | NoTemplateType Doc Position
    | NoMatchingTemplateOrProcedure -- ^ suitable template instantiation not found
        Doc -- ^ expected match
        [(Position,Doc,SecrecError)] -- ^ declared instantiations in scope
        Doc -- ^ variable bindings in scope
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
        Doc Doc -- types
        (Either Doc SecrecError) -- environment or sub-error
    | CoercionException -- ^ @coerces@ fails to prove equality
        Doc Doc -- types
        (Either Doc SecrecError) -- environment or sub-error
    | UnificationException -- ^ @unifies@ fails to unify two types
        Doc Doc -- types
        (Either Doc SecrecError) -- environment or sub-error
    | ComparisonException -- ^ @compares@ fails to compare two types
        Doc Doc -- types
        (Either Doc SecrecError) -- environment or sub-error
    | MultipleDefinedStruct -- ^ a struct is multiply defined
        Doc -- ^struct name
        Position -- ^existing definition
    | NonDeclassifiableExpression -- ^ an expression cannot be declassified
    | FieldNotFound -- ^ field not found in structure definition
        Doc -- ^ field name
    | NoDimensionForMatrixInitialization -- ^ no static dimension known for matrix initialization
        Identifier -- variable name
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
        Doc -- environment
    | ConflictingTemplateInstances
        Doc -- expected match
        [(Position,Doc)] -- duplicate declarations
        SecrecError -- sub-error
    | TemplateSolvingError -- error solving a template constraint
        SecrecError -- sub-error
    | StaticEvalError
        Doc -- expression
    | UnresolvedVariable
        Doc -- variable name
        Doc -- environment
    | UnresolvedMatrixProjection
        Doc -- ^ type
        Doc -- ^ ranges
        SecrecError -- ^ sub-error
    | MultipleTypeSubstitutions -- a variable can be resolved in multiple ways
        [PPDyn] -- list of different substitution options
  deriving (Show,Typeable,Data)

instance PP TypecheckerErr where
    pp e@(UnreachableDeadCode {}) = text (show e)
    pp e@(NonStaticDimension t err) = text "Array dimension must be statically known for type" <+> quotes t $+$ nest 4
        (text "Static evaluation error:" $+$ nest 4 (pp err))
    pp e@(MismatchingArrayDimension t d ds (Left proj)) = text "Mismatching dimensions for type" <+> quotes t <+> text "in projection" <+> proj <> char ':' $+$ nest 4
           (text "Expected:" <+> pp ds
        $+$ text "Actual:" <+> pp d)
    pp e@(MismatchingArrayDimension t d ds (Right (v,sz))) = text "Mismatching dimensions for type" <+> quotes t <+> text "in variable declaration" <+> v <+> text "with size" <+> sz <> char ':' $+$ nest 4
           (text "Expected:" <+> pp ds
        $+$ text "Actual:" <+> pp d)
    pp e@(MultipleDefinedVariable {}) = text (show e)
    pp e@(NoReturnStatement dec) = text "No return statement in procedure or operator declaration:" $+$ nest 4 dec
    pp e@(NoTemplateType {}) = text (show e)
    pp e@(NoMatchingTemplateOrProcedure ex defs ss) = text "Could not find matching template or procedure:" $+$ nest 4
           (text "Expected match:" <+> ex
        $+$ text "Actual declarations: " $+$ nest 4 (vcat (map (\(p,d,err) -> pp p <> char ':' $+$ nest 4 ((text "Declaration:" $+$ nest 4 d) $+$ (text "Instantiation error:" $+$ nest 4 (pp err)))) defs))
        $+$ text "With bindings: " $+$ nest 4 ss)
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
    pp e@(MultipleDefinedStructTemplate i p) = text (show e)
--        text "Overloaded templates for struct" <+> quotes (text i) <+> text "not supported:"
--        $+$ nest 4 (error "TODO")
    pp e@(EqualityException t1 t2 env) = text "Failed to prove equality:" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(CoercionException t1 t2 env) = text "Failed to apply implicit coercion:" $+$ nest 4
           (text "From:" <+> t1
        $+$ text "To:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(UnificationException t1 t2 env) = text "Failed to unify:" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(ComparisonException t1 t2 env) = text "Failed to compare:" $+$ nest 4
           (text "Left:" <+> t1
        $+$ text "Right:" <+> t2
        $+$ ppConstraintEnv env)
    pp e@(MultipleDefinedStruct {}) = text (show e)
    pp e@(NonDeclassifiableExpression {}) = text (show e)
    pp e@(FieldNotFound {}) = text (show e)
    pp e@(NoDimensionForMatrixInitialization {}) = text (show e)
    pp e@(ArrayAccessOutOfBounds t i rng) = text "Range selection" <+> rng <+> text "of the" <+> ppOrdinal i <+> text "dimension of type" <+> quotes t <+> text "out of bounds"
    pp e@(VariableNotFound {}) = text (show e)
    pp e@(InvalidToStringArgument {}) = text (show e)
    pp e@(InvalidSizeArgument {}) = text (show e)
    pp e@(DuplicateTemplateInstances ex defs ss) = text "Duplicate matching instances for template or procedure application:" $+$ nest 4
           (text "Expected match:" <+> ex
        $+$ text "Duplicate declarations: " $+$ nest 4 (vcat (map (\(p,d) -> pp p <> char ':' $+$ nest 4 d) defs))
        $+$ text "With bindings: " $+$ nest 4 ss)
    pp e@(ConflictingTemplateInstances ex defs err) = text "Conflicting matching instances for template or procedure application:" $+$ nest 4
           (text "Expected match:" <+> ex
        $+$ text "Conflicting declarations: " $+$ nest 4 (vcat (map (\(p,d) -> pp p <> char ':' $+$ nest 4 d) defs))
        $+$ text "Conflict: " $+$ nest 4 (pp err))
    pp (TemplateSolvingError err) = text "Failed to solve template instantiation:" $+$ nest 4
        (text "Because of:" $+$ nest 4 (pp err))
    pp (StaticEvalError e) = text "Unable to statically evaluate expression:" $+$ nest 4 e
    pp (UnresolvedVariable v env) = text "Unable to resolve variable: " <+> quotes v $+$ nest 4
        (text "With bindings: " $+$ nest 4 env)
    pp (UnresolvedMatrixProjection t rngs err) = text "Unable to resolve matrix projection:" $+$ nest 4
        ((text "Type:" <+> t <> rngs) $+$ (text "Error:" $+$ nest 4 (pp err)))
    pp (MultipleTypeSubstitutions opts) = text "Multiple type substitutions:" $+$ nest 4 (vcat $ map f $ zip [1..] opts)
        where f (i,ss) = text "Option" <+> integer i <> char ':' $+$ nest 4 (pp ss)

ppConstraintEnv (Left env) = text "With binginds:" $+$ nest 4 env
ppConstraintEnv (Right suberr) = text "Because of:" $+$ nest 4 (pp suberr)

data ModuleErr
    = DuplicateModuleName Identifier FilePath FilePath
    | ModuleNotFound Identifier
    | CircularModuleDependency [(Identifier,Identifier,Position)]
  deriving (Show,Read,Data,Typeable)

instance PP ModuleErr where
    pp (DuplicateModuleName i f1 f2) = text "Duplicate module" <+> quotes (text i) <> char ':' $+$ nest 4 (text f1 $+$ text f2)
    pp (ModuleNotFound i) = text "Module" <+> quotes (text i) <+> text "not found"
    pp (CircularModuleDependency g) = text "Circular module dependency:" $+$ nest 4 (vcat $ map ppNode g)
        where ppNode (from,to,l) = quotes (text from) <+> text "imports" <+> quotes (text to) <+> text "at" <+> pp l

moduleError :: Position -> ModuleErr -> SecrecError
moduleError = ModuleError

modError :: MonadError SecrecError m => Position -> ModuleErr -> m a
modError pos msg = throwError $ moduleError pos msg

genericError :: MonadError SecrecError m => Position -> Doc -> m a
genericError pos msg = throwError $ GenericError pos msg

typecheckerError :: Position -> TypecheckerErr -> SecrecError
typecheckerError = TypecheckerError

data SecrecWarning = TypecheckerWarning Position TypecheckerWarn
  deriving (Show,Typeable)
  
instance PP SecrecWarning where
    pp (TypecheckerWarning p w) = pp p <> text ": Warning:" $+$ nest 4 (pp w)
  
data TypecheckerWarn
    = UnusedVariable
        Doc -- ^ variable
    | DependentSizeSelection -- dependent size in selection
        Doc -- type
        Word64 -- dimension where the dependent size occurs
        (Maybe Doc) -- range selection
        SecrecError -- ^ sub-error
    | DependentMatrixSize
        Doc -- type
        Word64 -- size's dimension
        Doc -- dependent expression
        (Maybe Doc) -- variable declaration
        SecrecError -- ^ sub-error
    | DependentMatrixDimension
        Doc -- partial type
        Doc -- dependent expression
        (Maybe Doc) -- variable declaration
        SecrecError -- ^ sub-error
    | EmptyBranch
        Doc -- statement
    | SingleIterationLoop
        Doc -- statement
    | ShadowedVariable
        Doc -- ^ name of the shadowed variable
        Position -- ^ shadowed position
    | NoStaticDimension -- ^ matrix dimension not known at static time
        Doc -- type
        SecrecError -- ^ sub-eror
    | LiteralOutOfRange -- literal out of range
        String -- literal value
        Doc -- type
        String -- min range
        String -- max range
  deriving (Data,Show,Typeable)

instance PP TypecheckerWarn where
    pp w@(UnusedVariable v) = text "Unused variable" <+> quotes v
    pp w@(DependentSizeSelection t i Nothing err) = text "Array size of the" <+> ppOrdinal i <+> text "dimension is not statically know for type" <+> quotes t $+$ nest 4
        (text "Static evaluation error:" <+> pp err)
    pp w@(DependentSizeSelection t i (Just rng) err) = text "Range selection" <+> rng <+> text "of the" <+> ppOrdinal i <+> text "dimension is not statically know for type" <+> quotes t $+$ nest 4
        (text "Static evaluation error:" <+> pp err)
    pp w@(DependentMatrixSize t d e mb err) = text "Dependent array size" <+> quotes e <+> text "in the" <+> ppOrdinal d <+> text "dimension of type" <+> t <+> maybe empty (\v -> text "in the variable declaration of" <+> quotes v) mb $+$ nest 4
        (text "Static evaluation error:" <+> pp err)
    pp w@(DependentMatrixDimension t e mb err) = text "Dependent array dimension" <+> quotes e <+> text "for type" <+> t <+> maybe empty (\v -> text "in the variable declaration of" <+> quotes v) mb $+$ nest 4
        (text "Static evaluation error:" <+> pp err)
    pp w@(EmptyBranch s) = text "Conditional branch statement is empty:" $+$ s
    pp w@(SingleIterationLoop s) = text "Single iteration loop with body:" $+$ s
    pp w@(ShadowedVariable n p) = text "Variable" <+> quotes n <+> text "shadows definition from" <+> pp p
    pp w@(NoStaticDimension t err) = text "Array dimension not statically known for type" <+> quotes t $+$ nest 4
        (text "Static evaluation error:" <+> pp err)
    pp w@(LiteralOutOfRange lit ty min max) = text "Literal" <+> quotes (text lit) <+> text "out of the range" <+> brackets (text min <> text ".." <> text max) <+> text "for type" <+> quotes ty
