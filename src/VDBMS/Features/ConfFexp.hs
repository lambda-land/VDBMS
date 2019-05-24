-- | Coverts feature expressions to configs and back.
module VDBMS.Features.ConfFexp where

import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.Types (FeatureExpr)
import VDBMS.Features.FeatureExpr.Core (features)

------------------------ CONFIG 2 FEXP AND REVERSE ------------
------------------------ TODO: FILL OUT AFTER SIGMOD DEADLINE!!!
-- make this a tye class!

-- | generates a feature expression for the given configuration.
conf2fexp :: Config Bool -> FeatureExpr
-- Feature -> Bool -> FeatureExpr
conf2fexp c = undefined
  -- where 
  --   v = (Ref f <=> Lit b)

-- | generates a feature expr for the given list of configs.
confs2fexp :: [Config Bool] -> FeatureExpr
confs2fexp cs = undefined
-- foldl' Or (Lit False) $ conf2fexp cs

-- | extracts the valid configurations of a feature expr.
validConfsOfFexp :: FeatureExpr -> [Config Bool]
validConfsOfFexp f = undefined
  where
    fs = features f 



