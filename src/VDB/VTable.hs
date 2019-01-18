-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.VTable where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
-- import VDB.Algebra
import VDB.Name
-- import qualified VDB.FeatureExpr as F
-- import qualified VDB.Condition as C
-- import qualified VDB.Target as T
import VDB.Variational
-- import VDB.Type  
import VDB.Schema
-- import VDB.BruteForce.BruteForceSendQs
import VDB.SqlTable 

-- import Data.Map

-- import Database.HDBC

-- | the result of a vq is a variational table.
--   variational table data type.
data VTable = VTable TableSchema SqlTable


------------------- construct vtable for approach1 -------------------

-- | constructs a vtable from a sqlvtable. 
--   it generates the table schema and attaches it to the
--   sqltable of sqlvtable.
sqlVtable2VTable :: SqlVtable -> VTable
sqlVtable2VTable t = undefined

-- | constructs a vtable from a list sqlvtables.
-- 
sqlVtables2VTable :: [SqlVtable] -> VTable
sqlVtables2VTable ts = undefined

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
--   NOTES:
sqlVariantTables2VTable :: PresCondAtt -> [SqlVariantTable] -> VTable
sqlVariantTables2VTable p ts = VTable tabelSchema table 
  where
    tss = map constructSchemaFromSqlVariantTable ts -- [TableSchema]
    tabelSchema = combineTableSchema tss -- TableSchema
    ts' = map (flip conformSqlVariantTableToSchema $ getObj tabelSchema) ts -- [SqlVariantTable]
    ts'' = map (addTuplePresCond p) ts' -- [SqlTable]
    table = concat ts''





