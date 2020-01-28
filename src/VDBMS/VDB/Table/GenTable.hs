-- | Generates vtables from results of quereis.
module VDBMS.VDB.Table.GenTable (

        -- sqlVtables2VTable,
        -- sqlVariantTables2VTable,
        -- adjustVTable2TableSch
        varSqlTables2Table

) where 

import VDBMS.VDB.Table.Core (Table, mkVTable)
import VDBMS.VDB.Name (PCatt)
-- import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Variational.Schema (TableSchema)
import VDBMS.Features.Variant (Variant)
import VDBMS.DBMS.Table.SqlVtable (SqlVtable)
import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable)
-- import VDBMS.DBMS.Table.SqlVtableApplyFexpOps
import VDBMS.Features.FeatureExpr.FeatureExpr (Feature, FeatureExpr)
import VDBMS.DBMS.Table.Table (SqlTable)


-- 
-- TODO: PUT FUNCS IN RIGHT FILES!!!!!!!!!
-- 

-- | drops tuples that given config in the variant
--   their pres cond is unsat. the passed fexp is the
--   presence condition of the entire table.
dropUnsatTuples :: FeatureExpr -> SqlVariantTable -> SqlVariantTable
dropUnsatTuples f t = undefined

-- | drops the pc of tuples from a sqltable
dropPCAttFromTable :: PCatt -> SqlTable -> SqlTable
dropPCAttFromTable = undefined

-- | drops the pc of tuples from a SqlVariantTable (which is variant sqltable).
dropPCAttFromSqlTable :: PCatt -> SqlVariantTable -> SqlVariantTable
dropPCAttFromSqlTable = undefined

-- | takes the schema of a variational table (ie. tableschema)
--   and adds the key value pairs of attributes that are missing
--   from the variant table to it with the value NULL.
adjustSqlTable2TableSch :: TableSchema -> SqlVariantTable -> SqlVariantTable
adjustSqlTable2TableSch = undefined

-- | turns a sqltable to a sqlvtable.
-- type SqlVtable = Opt SqlTable
sqlTable2SqlVTable :: [Feature] -> SqlVariantTable -> SqlVtable
sqlTable2SqlVTable = undefined

-- | combines a list of sqltables s.t. it disjuncts the pc 
--   of the same tuple.
combineSqlTables :: [SqlTable] -> SqlTable
combineSqlTables = undefined

-- | takes everything needed to combine a list of variant sqltables
--   to a table.
varSqlTables2Table :: [Feature] -> FeatureExpr -> PCatt 
                   -> TableSchema 
                   -> [SqlVariantTable]
                   -> Table
varSqlTables2Table fs t_pc pc t_sch ts = undefined

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


