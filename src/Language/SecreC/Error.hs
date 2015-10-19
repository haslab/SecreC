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
    | ParsingException ParseError 
    deriving (Show,Typeable)

parserError :: ParserException -> SecrecError
parserError = ParserError

data SecrecError = TypecheckerError Position TypecheckerErr
                 | ParserError ParserException
                 | ModuleError Position ModuleErr
                 | GenericError String -- ^message
  deriving (Show,Typeable)

data TypecheckerErr
    = UnreachableDeadCode [Statement Position]
    | MismatchingArrayDimension Int Int (VarName Position)
    | MultipleDefinedVariable (VarName Position)
    | NoReturnStatement (Either (Op Position) (ProcedureName Position))
    | NoStaticDimension (Expression Position)
    | NoTemplateType (TypeName Position) Position
    | NoMatchingTemplate (TypeName Position) [TemplateTypeArgument Position] [Position]
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
    | DependentDimensionSize (Expression Position) (Maybe (VarName Position))
    | EmptyBranch (Statement Position)
    | SingleIterationLoop (Statement Position)
    | ShadowedVariable
        Identifier -- ^ name of the shadowed variable
        Position -- ^ shadowed position
  deriving (Show,Read,Data,Typeable)
