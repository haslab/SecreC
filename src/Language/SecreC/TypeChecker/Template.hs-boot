{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars

templateDecReturn :: (VarsTcM loc,Location loc) => loc -> DecType -> TcM loc Type

matchTemplate :: (VarsTcM loc,Location loc) => loc -> Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> TcM loc [EntryEnv loc] -> TcM loc (DecType,Maybe [VarName VarIdentifier Type])