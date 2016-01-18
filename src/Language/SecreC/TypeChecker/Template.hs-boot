{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars

templateDecReturn :: (VarsIdTcM loc m,Location loc) => loc -> DecType -> TcM loc m Type

matchTemplate :: (VarsIdTcM loc m,Location loc) => loc -> Bool -> TIdentifier -> Maybe [Type] -> Maybe [Expression VarIdentifier Type] -> Maybe Type -> TcM loc m [EntryEnv loc] -> TcM loc m (DecType,[VarName VarIdentifier Type])