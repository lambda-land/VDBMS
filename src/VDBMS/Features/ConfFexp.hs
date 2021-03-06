-- | Coverts feature expressions to configs and back.
module VDBMS.Features.ConfFexp (

       conf2fexp
       , confs2fexp

)where

import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.Types (FeatureExpr(..))
import VDBMS.Features.Feature (Feature)
-- import VDBMS.Features.FeatureExpr.Core (features)

-- @Eric: can this be a type class? if we were to extend variability representation?

-- | generates a feature expression for the given configuration.
conf2fexp :: [Feature] -> Config Bool -> FeatureExpr
-- Feature -> Bool -> FeatureExpr
conf2fexp fs c = 
  foldl (\fexp f -> if c f then (And fexp (Ref f)) 
                           else (And fexp (Not (Ref f))))
        (Lit True) 
        fs

-- | generates a feature expr for the given list of configs.
confs2fexp :: [Feature] -> [Config Bool] -> FeatureExpr
confs2fexp fs cs = foldl (\fexp c -> Or fexp (conf2fexp fs c)) (Lit False) cs




