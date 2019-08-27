-- | generates a relational query with the same schema
--   for each of the relational queries in a list without storing any
--   temporary result.
module VDBMS.QueryGen.MySql.GenMulQsSameSch where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql (SqlSelect)
import VDBMS.VDB.Schema.Variational.Schema (TableSchema, getTableSchAttsList)
import VDBMS.VDB.Schema.Relational.Types (RSchema)
import VDBMS.TypeSystem.Relational.TypeSystem (typeOfRQuery)
import VDBMS.VDB.Name (Attribute)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)

import Control.Monad.Catch 

-- | generates sql queries for relational queries based on
--   a given variational table schema. 
genQsSameSch :: TableSchema -> [RAlgebra] -> [SqlSelect]
genQsSameSch t qs = fmap ((adjustQSch as) . transAlgebra2Sql) qs
  where
    as = getTableSchAttsList t 
     -- ts <- mapM (uncurry typeOfRQuery) qss 
     -- let qs = fmap ((adjustQSch as) . transAlgebra2Sql . fst) qss
     -- return undefined

-- | adjusts the schema of a sql query wrt a given list of attribute.
adjustQSch :: [Attribute] -> SqlSelect -> SqlSelect
adjustQSch = undefined