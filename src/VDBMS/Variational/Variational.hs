-- | A generic interface for variational things.
module VDBMS.Variational.Variational (
        
        Variational(..)

) where

import VDBMS.Features.Config 
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name (Rename(..))
import VDBMS.Variational.Opt
import VDBMS.Features.ConfFexp (confs2fexp)

import Control.Arrow (first)
import Data.List (groupBy)

-- | The pair of a configuration attached to its
--   configured thing of a variational thing.
type Variant a = ((Config Bool), (NonVariational a))

-- | A group of variant things where their configurations
--   have been joined and constructed a feature expression.
type VariantGroup a = Opt (NonVariational a)

-- | A type class for variational things.
class Variational a where

  -- | The nonvariational correspondent of a.
  type NonVariational a :: *

  -- | Fully configure a variational thing and return the
  --   non-variational correspondent of it.
  configure :: Config Bool -> a -> NonVariational a

  -- | configures a variaitonal thing for all valid configurations
  --   possible and generates a map of configurations and their 
  --   nonvariational thing.
  vsem :: [Config Bool] -> a -> [Variant a]
  vsem cs a = map (\c -> (c, configure c a)) cs 

  -- | A more efficient vsem.
  vsem_ :: Eq (NonVariational a) 
        => [Config Bool] -> a -> [([Config Bool], NonVariational a)]
  vsem_ cs a = map pushdown $ groupBy (\o o' -> snd o == snd o') $ vsem cs a
    where
      -- pushdown :: [(Config Bool, NonVariational a)]
      --          -> ([Config Bool], NonVariational a)
      pushdown xs = foldr (\(c,_) (cs,x) -> (c:cs,x)) 
                          ([fst $ head xs], snd $ head xs) 
                          (tail xs)

  -- | Groups the configurations of a vsem into a feature 
  --   expression and attaches it to the non-variational 
  --   thing.
  optionalize :: Eq (NonVariational a)
              => [Config Bool] -> a -> [VariantGroup a]
  optionalize cs a = fmap (first confs2fexp) $ vsem_ cs a 

  -- | Optionalizes a variational thing in a more efficient manner.
  --   By generating a list of non-variational things with fexp 
  --   attached to them.
  optionalize_ :: a -> [VariantGroup a]

  -- | Linearizes a variational thing to a comprehensive 
  --   non-variational thing, if possible.
  linearize :: a -> NonVariational a

  -- | Maps a function to variants. 
  -- mapVariant :: (a -> b) -> Variant a -> Variant b

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



