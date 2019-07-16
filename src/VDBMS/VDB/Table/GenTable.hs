-- | Generates vtables from results of quereis.
module VDBMS.VDB.Table.GenTable (

        sqlVtables2VTable,
        sqlVariantTables2VTable,
        adjustVTable2TableSch

) where 

import VDBMS.VDB.Table.Core
import VDBMS.VDB.Name (PresCondAtt)
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Table.SqlVtable
import VDBMS.DBMS.Table.SqlVariantTable
import VDBMS.DBMS.Table.SqlVtableApplyFexpOps

------------------- construct vtable for approach1 -------------------

-- | constructs a vtable from a list sqlvtables.
--   it generates the table schema and attaches it to the
--   sqltables of sqlvtables.
--   NOTE: we have duplicate tuples for fexps, i.e. if I have
--	       tuple a, Or A B and I run two diff q for A and B then I'll have
--         a, A
--         a, B
--   ADD REMOVEDUPLICATE TO THE RESULT!
sqlVtables2VTable :: PresCondAtt -> [SqlVtable] -> Table
sqlVtables2VTable p ts = mkVTable tabelSchema table 
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
sqlVariantTables2VTable :: PresCondAtt -> [SqlVariantTable] -> Table
sqlVariantTables2VTable p ts = mkVTable tabelSchema table 
  where
    tss         = map constructSchemaFromSqlVariantTable ts -- [TableSchema]
    tabelSchema = combineTableSchema tss -- TableSchema
    ts'         = map (flip conformSqlVariantTableToSchema $ getObj tabelSchema) ts -- [SqlVariantTable]
    ts''        = map (addTuplePresCond p) ts' -- [SqlTable]
    table       = concat ts''



---------------adjusting a vtable to a table schema---------

-- | adjusts a vtable to a table schema.
adjustVTable2TableSch :: TableSchema -> Table -> Table
adjustVTable2TableSch = undefined




