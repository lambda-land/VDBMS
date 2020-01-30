-- | Sql variant table, configure applied to a sql table.
module VDBMS.DBMS.Table.SqlVariantTable (

        SqlVariantTable,
        applyConfVariantTable,
        applyConfVariantTables,
        -- dropRowsInVariantTable,
        dropPresInVariantTable,
        constructSchemaFromSqlVariantTable,
        conformSqlVariantTableToSchema,
        addTuplePresCond,
        dropUnsatTuples,
        sqlVariantTable2SqlVTable,
        combineSqlVariantTables

) where

import Data.Set (Set)
-- import qualified Data.Set as S

import qualified Data.Map.Strict as M

import VDBMS.Features.Variant 
import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Table.Table
import VDBMS.DBMS.Table.SqlVtable
import VDBMS.Variational.Opt

type SqlVariantTable = Variant SqlTable Bool

------------------- apply config ----------------------

-- | applies the variant config to the variant table and drops 
--   the rows that applying conf to their pc resulted in false.
applyConfVariantTable :: PCatt -> FeatureExpr -> SqlVariantTable -> SqlVariantTable
applyConfVariantTable p f t = updateVariant (applyConfTable c p f $ getVariant t) t
  where c = getConfig t

-- -- | drops rows with false pres cond in a variant table.
-- dropRowsInVariantTable :: PCatt -> Set Attribute -> SqlVariantTable -> SqlVariantTable
-- dropRowsInVariantTable p t = updateVariant (dropRows p $ getVariant (applyConfVariantTable p as t)) t
  -- where c = getConfig t

-- | applies the variant config to variant tables.
applyConfVariantTables :: PCatt -> FeatureExpr -> [SqlVariantTable] -> [SqlVariantTable]
applyConfVariantTables p f = fmap $ applyConfVariantTable p f

-- | drops rows with false pres cond over a list of variant tables.
-- dropRowsInVariantTables :: PCatt -> [SqlVariantTable] -> [SqlVariantTable]
-- dropRowsInVariantTables p = fmap $ dropRowsInVariantTable p 

-- | drops the pres key value of all rows in a variant table.
dropPresInVariantTable :: PCatt -> SqlVariantTable -> SqlVariantTable
dropPresInVariantTable p t = updateVariant (dropPresInTable p (getVariant t)) t

-- | generates the relation schema (rowtype) of a variant table.
constructSchemaFromSqlVariantTable :: [Feature] -> SqlVariantTable -> TableSchema
constructSchemaFromSqlVariantTable fs t = (fexp, rowType)
  where
    fexp    = conf2fexp fs $ getConfig t 
    table   = getVariant t
    rowType = constRowTypeOfSqlTable fexp table
-- constructSchemaFromSqlVariantTable :: SqlVariantTable -> TableSchema
-- constructSchemaFromSqlVariantTable t = (fexp, rowType)
--   where
--     fexp = conf2fexp $ getConfig t 
--     row = head $ getVariant t
--     row' = M.mapKeys (\s -> Attribute s) row 
--     row'' = M.map typeOf row'
--     rowType = M.map (\v -> (fexp,v)) row''

-- | forces a sqlvarianttable to conform to a table schema. i.e. 
--   it adds all attributes in the schema to the sqlvarianttable
--   with sqlnull.
--   TODO and DISCUSS WITH ERIC: maybe we should insert some specific
--                               value (like nothing) to specify that
--                               this value doesn't actually exist!
-- it is totally ok if tuples have presence condition attribute.
conformSqlVariantTableToSchema :: SqlVariantTable -> RowType -> SqlVariantTable
conformSqlVariantTableToSchema t r = updateVariant 
  (map (flip conformSqlRowToRowType r) $ getVariant t) t
    
-- | adds presence condition key and its value to each row
--   of the sqlvarianttable and turns it into a vtable.
--   Assumption: sqlvarianttable shouldn't have pres cond in its
--               attributes.
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
addTuplePresCond :: [Feature] -> PCatt -> SqlVariantTable -> SqlTable
addTuplePresCond fs p vt = insertAttValToSqlTable (Attribute $ presCondAttName p) fexp t
  where 
    fexp = fexp2sqlval $ conf2fexp fs $ getConfig vt
    t    = getVariant vt

-- | turns a sqltable to a sqlvtable.
sqlVariantTable2SqlVTable :: [Feature] -> SqlVariantTable -> SqlVtable
sqlVariantTable2SqlVTable fs t 
  = mkOpt (conf2fexp fs $ getConfig t) (getVariant t)


-- | combines a list of sqltables. it just appends tables for now.
-- TODO: s.t. it disjuncts the pc 
--   of the same tuple.
-- big assumption: the tables all have the same schema.
-- unionWithKey :: Ord k => (k -> a -> a -> a) -> Map k a -> Map k a -> Map k a
combineSqlVariantTables :: PCatt -> [SqlVariantTable] -> SqlTable
combineSqlVariantTables _ = foldr ((++) . getVariant) []
