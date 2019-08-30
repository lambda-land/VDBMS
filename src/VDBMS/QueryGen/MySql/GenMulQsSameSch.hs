-- | generates a relational query with the same schema
--   for each of the relational queries in a list without storing any
--   temporary result.
module VDBMS.QueryGen.MySql.GenMulQsSameSch (

       genQsSameSch
       , genQSameSch

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql (SqlSelect)
import VDBMS.VDB.Schema.Variational.Schema (TableSchema, getTableSchAttsList)
import VDBMS.VDB.Schema.Relational.Types (RSchema)
import VDBMS.TypeSystem.Relational.TypeSystem (RTypeEnv, rtypeEnvAtts)
import VDBMS.VDB.Name (Attribute)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.QueryLang.SQL.Pure.Ops

-- | generates sql queries for relational queries passed
--   with their type env based on
--   a given list of attribute.
genQsSameSch :: [Attribute] -> [(RAlgebra, RTypeEnv)] -> [SqlSelect]
genQsSameSch as qts = fmap (genQSameSch as) qts

-- | generates a sql query for a given relational algebra query
--   with a given schema (list of atts).
genQSameSch :: [Attribute] -> (RAlgebra, RTypeEnv) -> SqlSelect
genQSameSch as (q,t) =
  adjustQSch as (rtypeEnvAtts t) (transAlgebra2Sql q)
