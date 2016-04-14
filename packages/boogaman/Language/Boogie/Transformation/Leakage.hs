module Language.Boogie.Transformation.Leakage where

import Language.Boogie.AST
import Language.Boogie.Exts
import Language.Boogie.Analysis.Leakage
import Language.Boogie.Pretty
import Language.Boogie.PrettyAST
import Data.Generics

mkFree s = s { specFree = True }

-- | change leakage or non-leakage annotations
changeLeakageProgram :: Bool -> Program -> Program
changeLeakageProgram leak = everywhere (mkT chgSpec `extT` chgContract)
    where
    chgSpec :: SpecClause -> SpecClause
    chgSpec s@(SpecClause t False e) = if leak == hasLeakageAnn e then s else mkFree s
    chgSpec s = s
    
    chgContract :: Contract -> Contract
    chgContract c@(Requires False e) = if leak == hasLeakageAnn e then c else Requires True e
    chgContract c@(Ensures False e) = if leak == hasLeakageAnn e then c else Ensures True e
    chgContract c = c