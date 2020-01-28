-- | Coverts feature expressions to configs and back.
module VDBMS.Features.ConfFexp where

import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.Types (FeatureExpr)
import VDBMS.Features.Feature (Feature)
-- import VDBMS.Features.FeatureExpr.Core (features)

-- @Eric: can this be a type class? if we were to extend variability representation?

-- | generates a feature expression for the given configuration.
conf2fexp :: [Feature] -> Config Bool -> FeatureExpr
-- Feature -> Bool -> FeatureExpr
conf2fexp = undefined
  -- where 
  --   v = (Ref f <=> Lit b)

-- | generates a feature expr for the given list of configs.
confs2fexp :: [Feature] -> [Config Bool] -> FeatureExpr
confs2fexp = undefined
-- foldl' Or (Lit False) $ conf2fexp cs

-- | extracts the valid configurations of a feature expr.
validConfsOfFexp :: [Feature] -> FeatureExpr -> [Config Bool]
validConfsOfFexp fs fexp = undefined

-- the following is wrong b/c i could have true as a fexp ...
-- validConfsOfFexp f = undefined
--   where
--     fs = features f 



