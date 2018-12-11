-- | Variational database schemas.
module VDB.Schema where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set as S
import Data.Function (on)

import VDB.FeatureExpr
import VDB.Name
import VDB.Variational
import VDB.Type


-- | Type of a relation in the database.
-- type RowType = [Opt (Attribute, Type)]
type RowType = Map Attribute (Opt SqlType)


-- | Attributes must be unique in a table. The pair (Int, Attribute)
--   is for keeping the order of attributes in a relation.
type UniqeAttribute = (Int, Attribute)


-- | Type of a relation in the database. 
--type RelationSchema = Map UniqeAttribute (Opt Type)


-- | A schema is a mapping from relations to row types. Both the map itself and
--   each row type are optionally included. The top-level 'Opt' corresponds to
--   the feature model, which defines the set of valid configurations.
type Schema = Opt (Map Relation (Opt RowType))

-- | The feature model associated with a schema.
featureModel :: Schema -> FeatureExpr
featureModel (f,_) = f


-- | Get the schema of a relation in the database.
--lookupRelationSchema :: Relation -> Schema -> Maybe (Opt RelationSchema)
--lookupRelationSchema r (_,m) = M.lookup r m

-- | get attributes of a rowtype.
getRowTypeAtts :: RowType -> Set Attribute
getRowTypeAtts = M.keysSet

-- | get the attribute fexp from a rowtype
lookupAttFexpInRowType :: Attribute -> RowType -> Maybe FeatureExpr
lookupAttFexpInRowType a r = case M.lookup a r of 
                               Just (f,_) -> Just f
                               _ -> Nothing

-- | Get the fexp and type of an attribute in a rowtype
lookupAttFexpTypeInRowType :: Attribute -> RowType -> Maybe (Opt SqlType)
lookupAttFexpTypeInRowType = M.lookup

-- | Get attribute type pairs in a rowtype
getAttTypeFromRowType :: RowType -> Set (Attribute, SqlType)
getAttTypeFromRowType r = dropFexp rowSet
  where
    rowSet = S.fromList $ M.assocs r
    dropFexp :: (Ord a, Ord t) => Set (a,(o,t)) -> Set (a,t)
    dropFexp = S.map (\(a,(_,t)) -> (a,t)) 

-- | Get the schema of a relation in the database, where 
-- 	the relation schema is stored as a row type.
lookupRowType :: Relation -> Schema -> Maybe (Opt RowType)
lookupRowType r (_,m) = M.lookup r m


-- | Get the feature expression of a relation in a database.
lookupRelationFexp :: Relation -> Schema -> Maybe FeatureExpr
lookupRelationFexp r s = case lookupRowType r s of 
                           Just (f,_) -> Just f
                           _ -> Nothing


-- | Get the row type of a relation in a database.
lookupRel :: Relation -> Schema -> Maybe RowType
lookupRel r s = case lookupRowType r s of 
                  Just (_,rel) -> Just rel
                  _ -> Nothing

-- | Get the type and feature exp of an attribute in a database.
lookupAttribute :: Attribute -> Relation -> Schema -> Maybe (Opt SqlType)
lookupAttribute a r s = case lookupRowType r s of 
                          Just (_,rt) -> lookupAttFexpTypeInRowType a rt
                          _ -> Nothing

-- | helper func for lookupAttInRel -- apply new rowtypes
retrieve ::  Map Attribute (Opt SqlType) -> Attribute -> Maybe (FeatureExpr, SqlType)
retrieve m a = case M.toList m of 
                [] -> Nothing
                ((x,(y,z)):xs) -> if a == x then (Just (y,z)) else retrieve (M.fromList xs) a


-- | helper func for lookupAttInRel -- old
-- retrieve :: Eq b => [(a,(b,c))] -> b -> Maybe (a,c)
-- retrieve [] _ = Nothing
-- retrieve ((x,(y,z)):xs) v = if v == y then (Just (x,z)) else retrieve xs v

-- | Get the type of an attribute in a database.
lookupAttType :: Attribute -> Relation -> Schema -> Maybe SqlType
lookupAttType a r s = case lookupAttribute a r s of 
                        Just (_,t) -> Just t
                        _ -> Nothing

-- | Get the feature expression of an attribute in adatabase.
lookupAttFexp :: Attribute -> Relation -> Schema -> Maybe FeatureExpr
lookupAttFexp a r s = case lookupAttribute a r s of 
                        Just (f,_) -> Just f
                        _ -> Nothing


-- | Get all info of an attribute from a rowtype
--lookupAttInRel :: Attribute -> Relation -> Schema -> Maybe (Opt (Attribute,Type))
--lookupAttInRel a r s = case lookupRowType r s of
--                         Just (f,m) -> retrieve m a 
--                         _ -> Nothing

-- | lookup an attribute of a specific relation in database
--lookupAtt :: Attribute -> Relation -> Schema -> Maybe (Opt (Attribute,Type))
--lookupAtt a r s = case lookupRowType r s of 
--                    Just (f,l) -> lookupAttInRel a r s
--                    Just (o,(a,t))
--                    _ -> Nothing


-- | Lookup b in Map (a,b) v.
-- lookupSnd :: Eq b => b -> Map (a,b) c -> Maybe c
-- lookupSnd att M.fromLi(((id,att'),ft):ys) = if att == att' then (Just ft) else lookupSnd att (M.fromList ys)
-- lookupSnd _ empty = Nothing


-- | Get the type and feature exp of a unique attribute in a database.
--lookupUniqueAttribute :: UniqeAttribute -> Relation -> Schema -> Maybe (Opt Type)
--lookupUniqueAttribute ua r s = case lookupRelationSchema r s of 
--                                Just (_,rs) -> M.lookup ua rs
--                                _ -> Nothing


-- | Get the type and feature exp of an attribute in a database.
--lookupAttribute :: Attribute -> Relation -> Schema -> Maybe (Opt Type)
--lookupAttribute a r s = case lookupRelationSchema r s of 
--                          Just (_,rs) -> lookupSnd a rs
--                          _ -> Nothing



{-- | Get the type of an attribute in the database
lookupAttPresCond :: Attribute -> Relation -> Schema -> Maybe FeatureExpr
lookupAttPresCond a r s = case lookupAtt a r s of
                            Just (f,_) -> Just f
                            _ -> Nothing
--}
