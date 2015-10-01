{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

module Language.SecreC.Error where

import Language.SecreC.Position
import Language.SecreC.Syntax

import Data.Generics
import Control.Monad.Except
import Control.Monad.Writer

data ParserException 
    = LexicalException String
    | IdParserException String
    | ParsingException String 
    | EOFException
    deriving (Show,Read,Data,Typeable)
    
parserError :: Position -> String -> ParserException -> SecrecError
parserError = ParserError

data SecrecError = TypecheckerError Position TypecheckerErr
                 | ParserError Position String ParserException
                 | ModuleError Position ModuleErr
  deriving (Show,Read,Data,Typeable)

data TypecheckerErr
    = UnreachableDeadCode [Statement Position]
    | MismatchingArrayDimension Int Int (VarName Position)
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
    | DependentArraySize (Expression Position) (VarName Position)
    | EmptyBranch (Statement Position)
    | SingleIterationLoop (Statement Position)
  deriving (Show,Read,Data,Typeable)