-- | tranlates relational queries to sql.
module VDBMS.QueryGen.Sql.AlgebraToSql (

        genSql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.VDB.Name 
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List ((\\))

-- 
genSql :: RAlgebra -> SqlSelect
genSql = undefined