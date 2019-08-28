-- | generates one relational query for a given variational query without 
--   storing any temporary results.
module VDBMS.QueryGen.MySql.GenOneQ where 

import VDBMS.QueryGen.MySql.GenMulQsSameSch
import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql 
import VDBMS.VDB.Schema.Variational.Schema (TableSchema)
import VDBMS.VDB.Schema.Relational.Types (RSchema)


-- | generates a query from all queries generated with a same schema.
genQ :: TableSchema -> [(RAlgebra, RSchema)] -> SqlSelect
genQ t qss = foldr  (SqlBin SqlUnionAll) (head qs) (tail qs) 
  where 
    qs = genQsSameSch t qss 