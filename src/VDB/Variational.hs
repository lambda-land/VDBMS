module VDB.Variational where

import VDB.Config
import VDB.FeatureExpr
import VDB.Name


-- | A type class for variational things.
class Variational a where
  
  -- | Create a choice.
  choice :: FeatureExpr -> a -> a -> a
  
  -- | Partially configure a variational thing.
  select :: Feature -> Bool -> a -> a
    
  -- | Fully configure a variational thing.
  configure :: Config Bool -> a -> a


-- | A helper function to implement select for data types with simple choices.
selectHelper = undefined

-- | A helper function to implement configure for data types with simple choices.
configureHelper = undefined
