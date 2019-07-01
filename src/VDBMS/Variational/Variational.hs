-- | A generic interface for variational things.
module VDBMS.Variational.Variational (
        
        Variational(..)

) where

import VDBMS.Features.Config 
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name (Rename(..))
-- import VDBMS.Variational.Opt (mapSnd)
-- import VDBMS.Features.FeatureExpr.Types (FeatureExpr(..))
-- import VDBMS.Features.FeatureExpr.Core (evalFeatureExpr)
-- import VDBMS.Features.FeatureExpr.Ops (selectFeatureExpr)
-- import VDBMS.Features.Feature

-- | A type class for variational things.
class Variational a where

  -- | The nonvariational correspondent of a.
  type NonVariational a :: *

  -- | A configured thing with its configuration
  --   attached to it.
  -- type Configured a :: *

  -- | The variant of a variational thing, i.e., 
  --   the non-variational thing tagged with a fexp.
  type Variant a :: *

  -- | Fully configure a variational thing and return the
  --   non-variational correspondent of it.
  configure :: Config Bool -> a -> NonVariational a

  -- | configures a variaitonal thing for all valid configurations
  --   possible and generates a list of configured things.
  -- configr :: a ->  [Configured a]

  -- | Linearizes a variational thing by generating a list
  --   of non-variational things with fexp attached to them.
  linearize :: a -> [Variant a]

  -- | Maps a function to variants. 
  -- mapVariant :: (a -> b) -> Variant a -> Variant b

  -- | Linearized rename variaitonal. INCORRECT!
  -- linearizeRename :: Rename a -> [Variant (Rename a)]
  -- linearizeRename r = mapVariant () (Rename (name r)) $ linearize (thing r)

  -- | Map a function of non-variational things to
  --   variaitonal things. Basically lifts a non-variational
  --   function to the variational level.
  -- vmap :: (Variational a, Variational b) 
  --   => (NonVariational a -> NonVariational b)
  --   -> a -> b

  -- | configuring a variational thing first and applying
  --   a function on it is equivalent to applying that 
  --   function on the variational thing first and then
  --   configuring it.
  -- law: f (configure c v) = configure c ((vmap f) v)



