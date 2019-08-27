-- | generates a relational query with the same schema
--   for each of the relational queries in a list without storing any
--   temporary result.
module VDBMS.QueryGen.MySql.GenMulQsSameSch where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql (SqlSelect)
import VDBMS.VDB.Schema.Variational.Schema (TableSchema, getTableSchAttsList)
import VDBMS.VDB.Schema.Relational.Types (RSchema)

import Control.Monad.Catch 

-- | generates sql queries for relational queries based on
--   a given variational table schema. 
genQsSameSch :: MonadThrow m 
  => TableSchema -> [(RAlgebra, RSchema)] 
  -> [m SqlSelect]
genQsSameSch t qss =
  do let as = getTableSchAttsList t 
     ts <- mapM (uncurry typeOfRQuery) qss 
     return undefined

