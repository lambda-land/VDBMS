-- | Variational database schemas.
module VDB.Schema where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import VDB.FeatureExpr
import VDB.Name
import VDB.Variational
import VDB.Value


-- | Type of a relation in the database.
type RowType = [Opt (Attribute,Type)]

-- | A schema is a mapping from relations to row types. Both the map itself and
--   each row type are optionally included. The top-level 'Opt' corresponds to
--   the feature model, which defines the set of valid configurations.
type Schema = Opt (Map Relation (Opt RowType))

-- | The feature model associated with a schema.
featureModel :: Schema -> FeatureExpr
featureModel (f,_) = f

-- | Get the type of a relation in the database.
lookupRowType :: Relation -> Schema -> Maybe (Opt RowType)
lookupRowType r (_,m) = M.lookup r m
