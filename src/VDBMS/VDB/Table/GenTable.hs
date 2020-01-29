-- | Generates vtables from results of quereis.
module VDBMS.VDB.Table.GenTable (

        -- sqlVtables2VTable,
        -- sqlVariantTables2VTable,
        -- adjustVTable2TableSch
        variantSqlTables2Table

) where 

import VDBMS.VDB.Table.Core (Table, mkVTable)
import VDBMS.VDB.Name (PCatt)
-- import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema (TableSchema, tschFexp)
import VDBMS.Features.Variant (Variant)
import VDBMS.DBMS.Table.SqlVtable (SqlVtable)
import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable, 
  dropUnsatTuples, dropPresInVariantTable, conformSqlVariantTableToSchema,
  sqlVariantTable2SqlVTable)
-- import VDBMS.DBMS.Table.SqlVtableApplyFexpOps
import VDBMS.Features.FeatureExpr.FeatureExpr (Feature, FeatureExpr)
import VDBMS.DBMS.Table.Table (SqlTable)
import VDBMS.TypeSystem.Variational.TypeSystem (TypeEnv)

-- 
-- TODO: PUT FUNCS IN RIGHT FILES!!!!!!!!!
-- 
-- dropUnsatTuples :: FeatureExpr -> PCatt -> SqlVariantTable -> SqlVariantTable
-- dropPresInVariantTable :: PCatt -> SqlVariantTable -> SqlVariantTable
-- conformSqlVariantTableToSchema :: SqlVariantTable -> RowType -> SqlVariantTable
-- sqlVariantTable2SqlVTable :: [Feature] -> SqlVariantTable -> SqlVtable
-- combineSqlTables :: [SqlTable] -> SqlTable

-- | turns a type env to table schema.
-- typeenv2TableSchema :: TypeEnv -> TableSchema
-- typeenv2TableSchema = undefined

-- | takes everything needed to combine a list of variant sqltables
--   to a table.
variantSqlTables2Table :: [Feature] -> PCatt 
                       -> TableSchema
                       -> [SqlVariantTable]
                       -> Table
variantSqlTables2Table fs pc t_sch ts 
  = undefined
    -- where 
    --   t_pc = tschFexp t_sch
    --   ts_valid = map (dropUnsatTuples t_pc pc) ts

{--
------------------- construct vtable for approach1 -------------------

-- | constructs a vtable from a list sqlvtables.
--   it generates the table schema and attaches it to the
--   sqltables of sqlvtables.
--   NOTE: we have duplicate tuples for fexps, i.e. if I have
--	       tuple a, Or A B and I run two diff q for A and B then I'll have
--         a, A
--         a, B
--   ADD REMOVEDUPLICATE TO THE RESULT!
sqlVtables2VTable :: PCatt -> [SqlVtable] -> Table
sqlVtables2VTable _ ts = mkVTable tabelSchema table 
  where
    tss         = map constSchemaFromSqlVtable ts -- [TableSchema]
    tabelSchema = combineTableSchema tss -- TableSchema
    ts'         = map (flip conformSqlVtableToSchema $ getObj tabelSchema) ts -- [SqlVtable]
    table       = concat $ map getObj ts' -- doesn't remove duplicates!!
    -- table       = removeDuplicate p $ concat $ map getObj ts'

------------------- construct vtable for brute force -------------------
-- | takes a list of sqlvarianttables and constructs a vtable
--   from them to output to the user. 
--   steps:
--     1) construct the schema
--        a. construct schema from a sqlvarianttable 
--        b. combines the schemas from a
--     2) conform sqlvariant tables to the schema generated
--     3) add tuple pres cond to sqlvarianttables from 2
--     4) union all res of 3
--   NOTES: DOESN'T WORK RN DUE TO CONF2FEXP AND FEXP2CONF! 
--          TODO: FIX AFTER SIGMOD SUBMISSION!!!!
sqlVariantTables2VTable :: [Feature] -> PCatt -> [SqlVariantTable] -> Table
sqlVariantTables2VTable fs p ts = mkVTable tabelSchema table 
  where
    tss         = map (constructSchemaFromSqlVariantTable fs) ts -- [TableSchema]
    tabelSchema = combineTableSchema tss -- TableSchema
    ts'         = map (flip conformSqlVariantTableToSchema $ getObj tabelSchema) ts -- [SqlVariantTable]
    ts''        = map (addTuplePresCond fs p) ts' -- [SqlTable]
    table       = concat ts''



---------------adjusting a vtable to a table schema---------

-- | adjusts a vtable to a table schema.
adjustVTable2TableSch :: TableSchema -> Table -> Table
adjustVTable2TableSch = undefined

--}


