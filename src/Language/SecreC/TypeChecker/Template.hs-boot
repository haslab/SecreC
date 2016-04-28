{-# LANGUAGE FlexibleContexts #-}

module Language.SecreC.TypeChecker.Template where

import Language.SecreC.TypeChecker.Base
import Language.SecreC.Location
import Language.SecreC.Syntax
import Language.SecreC.Vars
import Language.SecreC.Prover.Base
import Language.SecreC.Position

matchTemplate :: (ProverK loc m) => loc -> Bool -> TIdentifier -> Maybe [(Type,IsVariadic)] -> Maybe [(Expression VarIdentifier Type,IsVariadic)] -> Maybe Type -> Maybe [VarName VarIdentifier Type] -> TcM m [EntryEnv] -> TcM m (DecType)