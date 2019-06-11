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

  -- | Create a choice.
  -- choice :: FeatureExpr -> a -> a -> a

  -- | Map a function over all choices.
  -- choiceMap :: (FeatureExpr -> a -> a -> a) -> a -> a

  -- | Partially configure a variational thing.
  -- select :: Feature -> Bool -> a -> a
  -- select f b = choiceMap (selectHelper f b)

  -- | Fully configure a variational thing and return the
  --   non-variational correspondent of it.
  configure :: Config Bool -> a -> NonVariational a

  -- | Map a function of non-variational things to
  --   variaitonal things.
  -- vmap :: (Variational b) 
  --   => (NonVariational a -> NonVariational b)
  --   -> a -> b

  -- configure :: C.Config Bool -> a -> b
  -- configure c = choiceMap (configureHelper c)


-- | A helper function to implement select for data types with simple choices.
-- selectHelper :: Variational a => Feature -> Bool -> FeatureExpr -> a -> a -> a
-- selectHelper f b e l r = case selectFeatureExpr f b e of
--     Lit b -> if b then l else r
--     e'    -> choice e' l r

-- -- | original: Lit b -> if b then l else r
-- -- | A helper function to implement configure for data types with simple choices.
-- configureHelper :: Config Bool -> FeatureExpr -> a -> a -> a
-- configureHelper c f l r = if evalFeatureExpr c f then l else r


-- Alex idea:
-- class V v where
--   type NV v :: *
--   type Config v :: *
--   config :: Config v -> v -> NV v
--   vmap :: (V u) => (NV v -> NV u) -> v -> u
--   law: f (config c v) = config c ((vmap f) v)



