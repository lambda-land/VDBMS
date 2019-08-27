-- | generates a relational query with its own independent schema
--   for each of the relational queries in a list without storing any
--   temporary result. 
-- Note that this approach requires us to clean up the tables we get
-- back from the database and adjust their schema into one unified
-- schema and accumulate all tuples into one table
module VDBMS.QueryGen.MySql.GenMulQsDiffSch (

       genQs

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql (SqlSelect)
import VDBMS.QueryTrans.AlgebraToSql

-- | simply translates a given relatinoal query to SQL.
genQs :: [RAlgebra] -> [SqlSelect]
genQs = fmap transAlgebra2Sql