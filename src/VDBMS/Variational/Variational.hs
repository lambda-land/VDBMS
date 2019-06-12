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

  -- | The nonvariational correspondent of a.
  type NonVariational a :: *

  -- type Configr a :: *
  -- | The variant of a variational thing, i.e., 
  --   the non-variational thing tagged with a fexp.
  type Variant a :: *


  -- | Fully configure a variational thing and return the
  --   non-variational correspondent of it.
  configure :: Config Bool -> a -> NonVariational a

  -- | Linearizes a variational thing by generating a list
  --   of non-variational things with fexp attached to them.
  linearize :: a -> [Variant a]

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



