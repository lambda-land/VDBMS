-- | Sql variant table, configure applied to a sql table.
module VDBMS.DBMS.SqlTable.SqlVariantTable (

        SqlVariantTable,
        applyConfVariantTable,
        applyConfVariantTables,
        dropRowsInVariantTable,
        dropPresInVariantTable,
        constructSchemaFromSqlVariantTable,
        conformSqlVariantTableToSchema,
        addTuplePresCond

) where

-- import Data.Map
-- import Data.Map.Strict (Map)
-- import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
-- import Data.List (deleteBy,groupBy)

import VDBMS.Features.Variant 
-- import VDBMS.Variational.Opt 
import VDBMS.VDB.Name
import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
import VDBMS.DBMS.Value.Value
-- import VDBMS.Features.SAT 
import VDBMS.DBMS.SqlTable.SqlTable

-- import Database.HDBC 

type SqlVariantTable = Variant SqlTable Bool

------------------- apply config ----------------------

-- | applies the variant config to the variant table.
applyConfVariantTable :: PresCondAtt -> Set Attribute -> SqlVariantTable -> SqlVariantTable
applyConfVariantTable p as t = updateVariant (applyConfTable c as p $ getVariant t) t
  where c = getConfig t

-- | drops rows with false pres cond in a variant table.
dropRowsInVariantTable :: PresCondAtt -> Set Attribute -> SqlVariantTable -> SqlVariantTable
dropRowsInVariantTable p as t = updateVariant (dropRows p $ getVariant (applyConfVariantTable p as t)) t
  where c = getConfig t

-- | applies the variant config to variant tables.
applyConfVariantTables :: PresCondAtt -> Set Attribute -> [SqlVariantTable] -> [SqlVariantTable]
applyConfVariantTables p as = fmap $ applyConfVariantTable p as

-- | drops rows with false pres cond over a list of variant tables.
-- dropRowsInVariantTables :: PresCondAtt -> [SqlVariantTable] -> [SqlVariantTable]
-- dropRowsInVariantTables p = fmap $ dropRowsInVariantTable p 

-- | drops the pres key value of all rows in a variant table.
dropPresInVariantTable :: PresCondAtt -> SqlVariantTable -> SqlVariantTable
dropPresInVariantTable p t = updateVariant (dropPresInTable p (getVariant t)) t

-- | generates the relation schema (rowtype) of a variant table.
constructSchemaFromSqlVariantTable :: SqlVariantTable -> TableSchema
constructSchemaFromSqlVariantTable t = (fexp, rowType)
  where
    fexp    = conf2fexp $ getConfig t 
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
conformSqlVariantTableToSchema :: SqlVariantTable -> RowType -> SqlVariantTable
conformSqlVariantTableToSchema t r = updateVariant 
  (map (flip conformSqlRowToRowType r) $ getVariant t) t
 --  where 
    
-- | adds presence condition key and its value to each row
--   of the sqlvarianttable and turns it into a vtable.
--   NOTE: sqlvarianttable shouldn't have pres cond in its
--         attributes.
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
addTuplePresCond :: PresCondAtt -> SqlVariantTable -> SqlTable
addTuplePresCond p vt = insertAttValToSqlTable (Attribute Nothing $ presCondAttName p) fexp t
  where 
    fexp = fexp2sqlval $ conf2fexp $ getConfig vt
    t    = getVariant vt



