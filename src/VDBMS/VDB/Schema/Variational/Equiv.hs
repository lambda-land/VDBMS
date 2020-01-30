-- | Variational database schema equivalency check.
module VDBMS.VDB.Schema.Variational.Equiv (

        equivConfigOnSchema

) where

import VDBMS.VDB.Schema.Variational.Types
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.Features.Config (Config, equivConfig)

-- | checks the equiv of two configs over a vschema.
--   TODO: need to add type constraint Boolean b!!
equivConfigOnSchema :: Schema a -> Config Bool -> Config Bool -> Bool
equivConfigOnSchema s c c' = equivConfig fs c c'
  where fs = features $ featureModel s

