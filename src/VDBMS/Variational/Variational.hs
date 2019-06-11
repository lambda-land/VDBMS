-- | A generic interface for variational things.
module VDBMS.Variational.Variational (
        
        Variational(..)

) where

import VDBMS.Features.Config 
import VDBMS.Features.FeatureExpr.FeatureExpr
-- import VDBMS.Features.FeatureExpr.Types (FeatureExpr(..))
-- import VDBMS.Features.FeatureExpr.Core (evalFeatureExpr)
-- import VDBMS.Features.FeatureExpr.Ops (selectFeatureExpr)
-- import VDBMS.Features.Feature

-- | A type class for variational things.
class Variational a where

  type NonVariational a :: *
  -- type Configr a :: *

  -- | Fully configure a variational thing and return the
  --   non-variational correspondent of it.
  configure :: Config Bool -> a -> NonVariational a

  -- | Map a function of non-variational things to
  --   variaitonal things.
  -- vmap :: (Variational b) 
  --   => (NonVariational a -> NonVariational b)
  --   -> a -> b

-- Alex idea:
-- class V v where
--   type NV v :: *
--   type Config v :: *
--   config :: Config v -> v -> NV v
--   vmap :: (V u) => (NV v -> NV u) -> v -> u
--   law: f (config c v) = config c ((vmap f) v)



