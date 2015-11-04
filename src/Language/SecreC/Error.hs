{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

module Language.SecreC.Error where

import Language.SecreC.Position
import Language.SecreC.Syntax
import Language.SecreC.Parser.Tokens

import Data.Generics
import Control.Monad.Except
import Control.Monad.Writer

import Text.Parsec

data ParserException 
    = LexicalException String
    | ParsecException ParseError 
    | DerpException String
    deriving (Show,Typeable)

parserError :: ParserException -> SecrecError
parserError = ParserError

data SecrecError = TypecheckerError Position TypecheckerErr
                 | ParserError ParserException
                 | ModuleError Position ModuleErr
                 | GenericError
                     Position -- ^ position
                     String -- ^message
  deriving (Show,Typeable)

data TypecheckerErr
    = UnreachableDeadCode [Statement Position]
    | NonStaticDimension -- ^ array dimension is not known statically
    | MismatchingArrayDimension -- ^ array dimension does not match sizes
        Integer -- defined dimension
        Integer -- expected dimension
        (Maybe (VarName Position)) -- name of the array variable
    | MultipleDefinedVariable (VarName Position)
    | NoReturnStatement (Either (Op Position) (ProcedureName Position))
    | NoTemplateType (TypeName Position) Position
    | NoMatchingTemplateOrProcedure -- ^ suitable template instantiation not found
        Identifier -- ^ template name
        [Position] -- ^ declared instantiations in scope
    | NotDefinedDomain Identifier
    | NotDefinedKind Identifier
    | InvalidDomainVariableName -- ^ a domain already exists with the declared domain variable name
        Identifier -- ^ variable name
        Position -- ^ domain declaration
    | InvalidTypeVariableName -- ^ a type already exists with the declared type variable name
        Identifier -- ^ variable name
        [Position] -- ^ type declarations
    | MultipleDefinedKind
        Identifier -- ^ kind name
        Position -- ^ position of the existing kind definition
    | NotDefinedType -- ^ type not found
        Identifier -- ^ type name
    | NotDefinedProcedure -- ^ procedure not found
        Identifier -- ^ procedure name
    | NoNonTemplateType -- ^ found a template type instead of a regular type
        Identifier -- ^ type name
    | MultipleDefinedDomain -- ^ a newly-declared domain already exists
        Identifier -- ^ domain name
        Position -- ^ Previous definition
    | MultipleDefinedField -- ^ a struct's field name is multiply defined
        Identifier -- ^ field name
        Position -- ^ previous definition
    | AmbiguousName -- ^ the same name refers to different entities
        Identifier -- ^ name
        [Position] -- ^ different declarations
    | MultipleDefinedStructTemplate -- ^ overloaded template structs not supported
        Identifier -- ^ template name
        Position -- ^ position of the already defined struct
    | EqualityException -- ^ @equals@ fails to prove equality
        String
    | CoercionException -- ^ @coerces@ fails to prove equality
        String
    | UnificationException -- ^ @unifies@ fails to unify two types
        String
    | ComparisonException -- ^ @compares@ fails to compare two types
        String
    | MultipleDefinedStruct -- ^ a struct is multiply defined
        Identifier -- ^struct name
        Position -- ^existing definition
    | NonDeclassifiableExpression -- ^ an expression cannot be declassified
    | FieldNotFound -- ^ field not found in structure definition
        Identifier -- ^ field name
    | NoDimensionForMatrixInitialization -- ^ no static dimension known for matrix initialization
        Identifier -- variable name
    | ArrayAccessOutOfBounds
        Integer -- array size
        (Integer,Integer) -- selection range
    | VariableNotFound -- variable not found in scope
        Identifier -- ^ variable name
    | NonSupportedOperation -- operation
        (Op ()) -- ^ operation
        String -- message
    | InvalidToStringArgument
    | InvalidSizeArgument
  deriving (Show,Read,Data,Typeable)

data ModuleErr
    = DuplicateModuleName Identifier FilePath FilePath
    | ModuleNotFound Identifier
    | CircularModuleDependency [(Identifier,Identifier,Position)]
  deriving (Show,Read,Data,Typeable)

moduleError :: Position -> ModuleErr -> SecrecError
moduleError = ModuleError

modError :: MonadError SecrecError m => Position -> ModuleErr -> m a
modError pos msg = throwError $ moduleError pos msg

genericError :: MonadError SecrecError m => Position -> String -> m a
genericError pos msg = throwError $ GenericError pos msg

typecheckerError :: Position -> TypecheckerErr -> SecrecError
typecheckerError = TypecheckerError

tcError :: MonadError SecrecError m => Position -> TypecheckerErr -> m a
tcError pos msg = throwError $ typecheckerError pos msg

tcWarn :: MonadWriter [SecrecWarning] m => Position -> TypecheckerWarn -> m ()
tcWarn pos msg = tell [TypecheckerWarning pos msg]

data SecrecWarning = TypecheckerWarning Position TypecheckerWarn
  deriving (Show,Read,Data,Typeable)
  
data TypecheckerWarn
    = UnusedVariable Identifier
    | DependentSizeSelection -- dependent size in selection
    | DependentMatrixSize (Expression Position) (Maybe (VarName Position))
    | EmptyBranch (Statement Position)
    | SingleIterationLoop (Statement Position)
    | ShadowedVariable
        Identifier -- ^ name of the shadowed variable
        Position -- ^ shadowed position
    | NoStaticDimension -- ^ matrix dimension not known at static time
        (Expression Position)
    | LiteralOutOfRange -- literal out of range
        String -- literal value
        String -- type
        String -- min range
        String -- max range
  deriving (Show,Read,Data,Typeable)
