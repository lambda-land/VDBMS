module VDB.Variational where

import VDB.Config
import VDB.FeatureExpr
import VDB.Name


-- | A type class for variational things.
class Variational a where

  -- | Create a choice.
  choice :: FeatureExpr -> a -> a -> a

  -- | Map a function over all choices.
  choiceMap :: (FeatureExpr -> a -> a -> a) -> a -> a

  -- | Partially configure a variational thing.
  select :: Feature -> Bool -> a -> a
  select f b = choiceMap (selectHelper f b)

  -- | Fully configure a variational thing.
  configure :: Config Bool -> a -> a
  configure c = choiceMap (configureHelper c)


-- | A helper function to implement select for data types with simple choices.
selectHelper :: Variational a => Feature -> Bool -> FeatureExpr -> a -> a -> a
selectHelper f b e l r = case selectFeatureExpr f b e of
    Lit b -> if b then l else r
    e'    -> choice e' l r

-- | A helper function to implement configure for data types with simple choices.
configureHelper :: Config Bool -> FeatureExpr -> a -> a -> a
configureHelper c f l r = if evalFeatureExpr c f then l else r
