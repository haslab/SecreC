{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars

matchTemplate :: (VarsTcM loc,Location loc) => loc -> TIdentifier -> Maybe [Type] -> Maybe [Type] -> Maybe Type -> TcM loc [EntryEnv loc] -> TcM loc DecType