-- | Representation of tuples and tables for interpreting variational queries.
module VDB.Table where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as Set

import VDB.FeatureExpr
import VDB.Name
import VDB.SAT
import VDB.Schema
import VDB.Variational
import VDB.Type

import Database.HDBC (SqlValue)

-- | A database is a mapping from relations to tables.
type Database = (Schema, Map Relation Table)

-- | A table is a list of tuples.
type Table = [Tuple]

-- | A table with an assigned feature exp for when 
--   you're returning a table without an assigned name
--   (relation) to it. 
type VTable = Opt Table

-- | A tuple is an optional map between attributes 
--   and their sqlvalues, where each value may be 
--   Nothing if the corresponding attribute is not 
--   present in a configuration.
type Tuple = Opt (Map Attribute (Maybe SqlValue))


-- | gets the tuple presence condition.
getTupleFexp :: Tuple -> FeatureExpr
getTupleFexp (o,_) = o

-- | gets the name of attributes of a tuple except 
--   the presence condition attribute name.
getTupleAtts :: Tuple -> PresCondAtt -> Set Attribute
getTupleAtts (_,as) p = Set.filter 
                         (\a -> attributeName a == presCondAttName p) 
                         (M.keysSet as)

-- | gets the type of the attributes of a tuple
--   except for the presence condition attribute.
-- getTupleAttTypes :: Tuple -> PresCondAtt -> Set (Attribute, Type)
-- getTupleAttTypes (_,as) p = filter (\a -> fst a == p)

-- | gets the schema of VDB.
getSchema :: Database -> Schema
getSchema = fst

-- | gets data of VDB.
getData :: Database -> Map Relation Table
getData = snd

-- | gets table assigned to a relation in a VDB.
getTable :: Database -> Relation -> Maybe Table
getTable db r = M.lookup r (getData db)

-- | gets table fexp.
getVTableFexp :: VTable -> FeatureExpr
getVTableFexp = fst


-- | Check a value against the attribute-type pair in a row type.
checkValue :: FeatureExpr -> Attribute -> Opt SqlType -> Maybe SqlValue -> Bool
checkValue ctx a (p,t) Nothing  = unsatisfiable (And ctx p)
checkValue ctx a (p,t) (Just v) = satisfiable (And ctx p) 
  -- && (t == typeOf v || typeOf v == TNull) -- need to be added
  -- for sqltype and sqlvalue

-- | Check a tuple against a row type. Ensures that the list of 
--   attributes in rowtype and tuples are the same. checks sat
--   of attPrescond and tuplePresCond
checkTuple :: FeatureExpr -> PresCondAtt -> RowType -> Tuple -> Bool
checkTuple ctx p row t = getTupleAtts t p == getRowTypeAtts row
  && and (M.elems checkValues) 
  where 
    checkValues :: Map Attribute Bool
    checkValues = M.intersectionWithKey (checkValue attPresCondAndTuplePresCond) 
                                      row (snd t)
    attPresCondAndTuplePresCond = And ctx (fst t)

-- | Validate a table against its row type. When checking
--   the initialized VDB ctx will be the rowtype fexp.
checkTable :: FeatureExpr -> PresCondAtt -> RowType -> Table -> Bool
checkTable ctx p row ts = all (checkTuple ctx p row) ts

-- | Validate a database against its schema. Have to check
--   the VDB after instantiate it.
checkDatabase :: Database -> PresCondAtt -> Bool
checkDatabase db p = and (M.mapWithKey checkRelation dbData)
  where 
    schema = getSchema db 
    dbData = getData db
    checkRelation relation table
      | Just row <- lookupRel relation (schema)
        = case lookupRelationFexp relation schema of
            Just fexp -> checkTable (And (featureModel schema) fexp) p row table
            _ -> False
      | otherwise = False

-- checkDatabase (fm,rows) db = M.size rows == M.size db
--     && and (M.mapWithKey checkRelation rows)
--   where
--     checkRelation name (p,row)
--       | Just table <- M.lookup name db = checkTable (And fm p) row table
--       | otherwise = False
 
