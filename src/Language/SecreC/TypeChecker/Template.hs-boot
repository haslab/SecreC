{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Prover.Base
import Language.SecreC.Position

localTemplate :: (ProverK loc m) => loc -> EntryEnv -> TcM m EntryEnv

matchTemplate :: (ProverK loc m) => loc -> Int -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Either Expr Type,IsVariadic)] -> Maybe Type -> TcM m [EntryEnv] -> TcM m DecType