-- | Generates vtables from results of quereis.
module VDBMS.VDB.Table.GenTable (

        -- sqlVtables2VTable,
        -- sqlVariantTables2VTable,
        -- adjustVTable2TableSch
        variantSqlTables2Table
        , sqlVtables2VTable

) where 

import VDBMS.VDB.Table.Core (Table, mkVTable)
import VDBMS.VDB.Name (PCatt)
-- import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema (TableSchema, tschFexp, tschRowType)
import VDBMS.Features.Variant (Variant)
import VDBMS.DBMS.Table.SqlVtable (SqlVtable, applyFexpToSqlVtable,
  updateTuplesPCInSqlVtable)
import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable, 
  applyConfVariantTables,
  updateTuplesPC)
-- import VDBMS.DBMS.Table.SqlVtableApplyFexpOps
import VDBMS.Features.FeatureExpr.FeatureExpr (Feature, FeatureExpr)
import VDBMS.DBMS.Table.Table (SqlTable, combineSqlTables, 
  conformSqlTableToSchema)
import VDBMS.TypeSystem.Variational.TypeSystem (TypeEnv)

-- | takes everything needed to combine a list of variant sqltables
--   to a table.
variantSqlTables2Table :: [Feature] -> PCatt 
                       -> TableSchema
                       -> [SqlVariantTable]
                       -> Table
variantSqlTables2Table fs pc t_sch ts 
  = mkVTable t_sch (combineSqlTables pc ts_sameSch_updatedPC)
    where 
      t_pc = tschFexp t_sch
      rowtype = tschRowType t_sch
      ts_valid = applyConfVariantTables pc t_pc ts
      ts_sameSch_updatedPC = map 
        ((flip conformSqlTableToSchema rowtype) . (updateTuplesPC fs pc)) 
        ts_valid

-- | takes everything neede to combine a list of opt sqltable
--   to a table.
sqlVtables2VTable :: PCatt -> TableSchema -> [SqlVtable] -> Table
sqlVtables2VTable pc t_sch ts 
  = mkVTable t_sch (combineSqlTables pc ts_sameSch_updatedPC)
    where
      t_pc = tschFexp t_sch
      rowtype = tschRowType t_sch
      ts_valid = map (applyFexpToSqlVtable t_pc pc) ts 
      ts_sameSch_updatedPC 
        = map ((flip conformSqlTableToSchema rowtype) 
               . (updateTuplesPCInSqlVtable pc)) 
              ts_valid

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


