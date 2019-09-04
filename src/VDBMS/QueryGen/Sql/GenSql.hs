-- | tranlates relational queries to sql.
module VDBMS.QueryGen.Sql.GenSql (

        genSql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.VDB.Name 
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List ((\\))

type FreshName = Int 

-- -- | A Query monad provides unique names (aliases)
-- --   and constructs a SqlSelect.
type QState = (SqlSelect, FreshName)
data Query a = Query (QState -> (a, QState))

-- 
genSql :: RAlgebra -> SqlSelect
genSql = undefined