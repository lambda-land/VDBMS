-- | Representation of tuples and tables for interpreting variational queries.
module VDB.Table where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import VDB.FeatureExpr
import VDB.Name
import VDB.SAT
import VDB.Schema
import VDB.Variational
import VDB.Value


-- | A database is a mapping from relations to tables.
type Database = Map Relation Table

-- | A table is a list of tuples.
type Table = [Tuple]

-- | A tuple is an optional list of values, where each value may be Nothing if
--   the corresponding attribute is not present in this configuration.
type Tuple = Opt [Maybe Value]


-- | Check a value against the attribute-type pair in a row type.
checkValue :: FeatureExpr -> Opt (Attribute,Type) -> Maybe Value -> Bool
checkValue ctx (p,_)     Nothing  = unsatisfiable (And ctx p)
checkValue ctx (p,(_,t)) (Just v) = satisfiable (And ctx p) && t == typeOf v

-- | Check a tuple against a row type.
checkTuple :: FeatureExpr -> RowType -> Tuple -> Bool
checkTuple ctx row (p,vs) = length row == length vs
    && and (zipWith (checkValue (And ctx p)) row vs)

-- | Validate a table against its row type.
checkTable :: FeatureExpr -> RowType -> Table -> Bool
checkTable ctx row ts = all (checkTuple ctx row) ts

-- | Validate a database against its schema.
checkDatabase :: Schema -> Database -> Bool
checkDatabase (fm,rows) db = M.size rows == M.size db
    && and (M.mapWithKey checkRelation rows)
  where
    checkRelation name (p,row)
      | Just table <- M.lookup name db = checkTable (And fm p) row table
      | otherwise = False
 
