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

-- | Get the feature expression of a relation
lookupRelation :: Relation -> Schema -> Maybe FeatureExpr
lookupRelation r s = case lookupRowType r s of 
                       Just (f,_) -> Just f
                       _ -> Nothing

-- | helper func for lookupAttInRel
retrieve :: Eq b => [(a,(b,c))] -> b -> Maybe (a,(b,c))
retrieve [] _ = Nothing
retrieve ((x,(y,z)):xs) v = if v == y then (Just (x,(y,z))) else retrieve xs v

-- | Get all info of an attribute from a rowtype
lookupAttInRel :: Attribute -> Relation -> Schema -> Maybe (Opt (Attribute,Type))
lookupAttInRel a r s = case lookupRowType r s of
                         Just (f,m) -> retrieve m a 
                         _ -> Nothing

-- | lookup an attribute of a specific relation in database
lookupAtt :: Attribute -> Relation -> Schema -> Maybe (Opt (Attribute,Type))
lookupAtt a r s = case lookupRowType r s of 
                    Just (f,l) -> lookupAttInRel a r s
--                    Just (o,(a,t))
                    _ -> Nothing

-- | Get the type of an attribute in the database
lookupAttPresCond :: Attribute -> Relation -> Schema -> Maybe FeatureExpr
lookupAttPresCond a r s = case lookupAtt a r s of
                            Just (f,_) -> Just f
                            _ -> Nothing

