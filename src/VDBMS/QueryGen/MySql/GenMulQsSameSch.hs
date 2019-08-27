-- | generates a relational query with the same schema
--   for each of the relational queries in a list without storing any
--   temporary result.
module VDBMS.QueryGen.MySql.GenMulQsSameSch where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql (SqlSelect)
import VDBMS.VDB.Schema.Variational.Schema (TableSchema, getTableSchAttsList)

-- | generates sql queries for relational queries based on
--   a given variational table schema. 
genQsSameSch :: TableSchema -> [RAlgebra] -> [SqlSelect]
genQsSameSch t qs = undefined
  where
    as = getTableSchAttsList t 

