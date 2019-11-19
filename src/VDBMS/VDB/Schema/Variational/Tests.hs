-- | Tests to check validity of a vschema. 
module VDBMS.VDB.Schema.Variational.Tests (

        isVschValid

) where

import VDBMS.Features.SAT
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
import VDBMS.Variational.Opt 

import Control.Monad.Catch 
import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Data.Map.Strict (toList)
import Control.Monad (foldM)

-- | Errors for schema validity checks.
data SchValErr 
  = FMunsat FeatureExpr
  | RelPCunsat Relation FeatureExpr
  | AttPCunsat Attribute FeatureExpr
  deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception SchValErr

-- | checks 1) if fm is sat, 2) if all relations
--   pc are sat, and 3) if all atts pc are sat.
isVschValid :: MonadThrow m => Schema -> m Bool 
isVschValid s = undefined

-- | checks if the feature model is satisfiable. 
satFM :: MonadThrow m => Schema -> m Bool 
satFM s
  | (satisfiable . featureModel) s == True = return True
  | otherwise = throwM $ FMunsat (featureModel s)

-- | checks if a relation pc is satisfiable. 
satRPC :: MonadThrow m => FeatureExpr -> (Relation, TableSchema) -> m Bool 
satRPC = undefined

-- | checks all relations in a schema to see if
--   their pc is satisfiable.
satRsPC :: MonadThrow m => Schema -> m Bool 
satRsPC s = foldM (\f p -> satRPC fm p >>= return . ((&&) f)) True sList
  where
    sList = (toList . getObj) s 
    fm = featureModel s

-- | checks if an attribute pc is satisfiable.


-- | checks if all attributes of a relation have 
--   satisfiable pc.

-- | check if all attributes of all relations of 
--   the schema have satisfiable pc.
