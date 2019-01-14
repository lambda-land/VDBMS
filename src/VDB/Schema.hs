-- | Variational database schemas.
module VDB.Schema where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function (on)
import Data.SBV (Boolean(..))
import Control.Arrow (first, second)

import VDB.FeatureExpr
import VDB.Name
import VDB.Variational
import VDB.Type
import VDB.Config (Config)

-- | Type of a relation in the database.
-- type RowType = [Opt (Attribute, Type)]
type RowType = Map Attribute (Opt SqlType)


-- | Attributes must be unique in a table. The pair (Int, Attribute)
--   is for keeping the order of attributes in a relation.
-- type UniqeAttribute = (Int, Attribute)


-- | Type of a relation in the database. 
--type RelationSchema = Map UniqeAttribute (Opt Type)


-- | A schema is a mapping from relations to row types. Both the map itself and
--   each row type are optionally included. The top-level 'Opt' corresponds to
--   the feature model, which defines the set of valid configurations.
type Schema = Opt (Map Relation (Opt RowType))

-- | The feature model associated with a schema.
featureModel :: Schema -> FeatureExpr
featureModel = getFexp

-- | Gets the structure of schema.
schemaStrct :: Schema -> Map Relation (Opt RowType)
schemaStrct = getObj 

-- | Get the schema of a relation in the database.
--lookupRelationSchema :: Relation -> Schema -> Maybe (Opt RelationSchema)
--lookupRelationSchema r (_,m) = M.lookup r m

-- | returns a relation arity.
relArity :: Relation -> Schema -> Int 
relArity r s = case rt of 
                 Just rowType -> M.size rowType
                 _ -> 0
  where 
    rt = lookupRel r s

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
    rowSet = Set.fromList $ M.assocs r
    dropFexp :: (Ord a, Ord t) => Set (a,(o,t)) -> Set (a,t)
    dropFexp = Set.map (\(a,(_,t)) -> (a,t)) 

-- | Get the schema of a relation in the database, where 
-- 	the relation schema is stored as a row type.
lookupRowType :: Relation -> Schema -> Maybe (Opt RowType)
lookupRowType r (_,m) = M.lookup r m

-- | gets valid relations of a schema. i.e. relations that
--   their fexp isn't false.
getRels :: Schema -> Set Relation
getRels s = Set.filter (flip validRel $ s) rels
  where 
    rels = M.keysSet $ schemaStrct s
    validRel :: Relation -> Schema -> Bool
    validRel r s 
      | lookupRelationFexp r s == Just (Lit False) = False
      | lookupRelationFexp r s == Nothing = False
      | otherwise = True


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

-- | apply config to fexp of schema.
appConfSchemaFexp :: Config Bool -> Schema -> Bool
-- appConfSchemaFexp c s = evalFeatureExpr c (featureModel s)
-- appConfSchemaFexp c s = evalFeatureExpr c $ featureModel s
appConfSchemaFexp c = evalFeatureExpr c . featureModel

-- | applies a config to a schema. Note that it keeps the 
--   attributes and relations that aren't valid in a variant
--   associated to the config.
appConfSchema :: Config Bool -> Schema -> Schema
appConfSchema c s 
  | schemaPres = (Lit (schemaPres), 
  M.map (appConfRowType c) (schemaStrct s))
  | otherwise = error "the schema doesn't exist for the given config!"
  where 
    schemaPres = appConfSchemaFexp c s

-- | applies a config to a schema. Note that it filters out 
--   invalid objects. 
appConfSchema' :: Config Bool -> Schema -> Schema
appConfSchema' c s = mkOpt (featureModel s) 
  (M.filter (\optRow -> getFexp optRow == Lit True) $ schemaStrct s)

-- | apply config to a rowtype. it doesn't filter out invalid attributes.
appConfRowType :: Config Bool -> Opt RowType -> Opt RowType
appConfRowType c (f,r) = (Lit (evalFeatureExpr c f),
  M.map (first $ Lit . evalFeatureExpr c) r)
--  M.map (\(f,t) -> (Lit (evalFeatureExpr c f),t)) r 

-- | apply config to a rowtype. it filters out invalid attributes.
appConfRowType' :: Config Bool -> Opt RowType -> Opt RowType
appConfRowType' c r = mkOpt (getFexp r) (M.filter 
  (\optType -> getFexp optType == Lit True) $ getObj r)
  -- (Lit (evalFeatureExpr c f),
  -- M.map (first $ Lit . evalFeatureExpr c) r)
--  M.map (\(f,t) -> (Lit (evalFeatureExpr c f),t)) r 



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
