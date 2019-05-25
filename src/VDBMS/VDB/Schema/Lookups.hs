-- | Variational database schema look up operations.
module VDBMS.VDB.Schema.Lookups (

        lookupAttFexpInRowType,
        lookupAttFexpTypeInRowType,
        lookupRowType,
        lookupRelationFexp,
        lookupRel,
        lookupRelAttsList,
        lookupAttType,
        lookupAttFexp

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import VDBMS.VDB.Schema.Types
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
import VDBMS.Variational.Opt
import VDBMS.DBMS.Type (SqlType)

-- | gets the attribute fexp conjoind with the table pres cond
--   from a table schema
-- lookupAttFexpInTableSch :: Attribute -> TableSchema -> Maybe FeatureExpr
-- lookupAttFexpInTableSch a (tf,tr) = case M.lookup a tr of 
--                                Just (f,_) 
--                                  | satisfiable f' -> Just f'
--                                  | otherwise -> Nothing
--                                    where f' = And tf f
--                                _ -> Nothing

-- -- | gets the attribute pres cond conjoined with the table pres cond
-- --   and the attribute type from a table schema.
-- lookupAttFexpTypeInTableSch :: Attribute -> TableSchema -> Maybe (Opt SqlType)
-- lookupAttFexpTypeInTableSch a (tf,tr) = case M.lookup a tr of 
--                                           Just (f,t)
--                                             | satisfiable f' -> Just (f',t)
--                                             | otherwise -> Nothing
--                                               where f' = And tf f 
--                                           _ -> Nothing

-- | get the attribute fexp from a rowtype
lookupAttFexpInRowType :: Attribute -> RowType -> Maybe FeatureExpr
lookupAttFexpInRowType a r = case M.lookup a r of 
                               Just (f,_) -> Just f
                               _ -> Nothing

-- | Get the fexp and type of an attribute in a rowtype
lookupAttFexpTypeInRowType :: Attribute -> RowType -> Maybe (Opt SqlType)
lookupAttFexpTypeInRowType = M.lookup

-- | Get the schema of a relation in the database, where 
-- 	the relation schema is stored as a row type.
lookupRowType :: Relation -> Schema -> Maybe (TableSchema)
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

-- | get the attributes of a relation in a database.
lookupRelAttsList :: Relation -> Schema -> Maybe [Attribute]
lookupRelAttsList r s = M.keys <$> lookupRel r s

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
