-- | generates one relational query for a given variational query without 
--   storing any temporary results.
module VDBMS.QueryGen.MySql.GenOneQ where 

import VDBMS.QueryGen.MySql.GenMulQsSameSch
import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql (SqlSelect)
import VDBMS.VDB.Name (Attribute)
import VDBMS.TypeSystem.Relational.TypeSystem (RTypeEnv)


-- | generates a query from all queries generated with a same 
--   list of attribute.
genQ :: [Attribute] -> [(RAlgebra, RTypeEnv)] -> SqlSelect
genQ t qss = foldr  (SqlBin SqlUnionAll) (head qs) (tail qs) 
  where 
    qs = genQsSameSch t qss 