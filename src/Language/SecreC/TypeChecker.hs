{-# LANGUAGE DeriveDataTypeable #-}

module Language.SecreC.TypeChecker where

import Language.SecreC.Monad
import Language.SecreC.Error
import Language.SecreC.Syntax
import Language.SecreC.Location
import Language.SecreC.Position

import Data.Generics



tcModules :: [Module loc] -> Tc loc [Module (Typed loc)]
tcModules = mapM tcModule

tcModule :: Module loc -> TC loc (Module (Typed loc))
tcModule (Module name prog) = do
    prog' <- tcProgram prog
    return $ Module (noTypeLoc name) prog'

tcProgram :: Program loc -> TC loc (Program (Typed loc))
tcProgram = undefined

