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
  deriving (Eq, Show)

------------------- construct vtable for approach1 -------------------

-- | constructs a vtable from a list sqlvtables.
--   it generates the table schema and attaches it to the
--   sqltables of sqlvtables.
--   NOTE: we have duplicate tuples for fexps, i.e. if I have
--	       tuple a, Or A B and I run two diff q for A and B then I'll have
--         a, A
--         a, B
--   ADD REMOVEDUPLICATE TO THE RESULT!
sqlVtables2VTable :: PresCondAtt -> [SqlVtable] -> VTable
sqlVtables2VTable p ts = VTable tabelSchema table 
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
sqlVariantTables2VTable :: PresCondAtt -> [SqlVariantTable] -> VTable
sqlVariantTables2VTable p ts = VTable tabelSchema table 
  where
    tss         = map constructSchemaFromSqlVariantTable ts -- [TableSchema]
    tabelSchema = combineTableSchema tss -- TableSchema
    ts'         = map (flip conformSqlVariantTableToSchema $ getObj tabelSchema) ts -- [SqlVariantTable]
    ts''        = map (addTuplePresCond p) ts' -- [SqlTable]
    table       = concat ts''





