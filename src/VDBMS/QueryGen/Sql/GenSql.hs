-- | tranlates relational queries to sql.
module VDBMS.QueryGen.Sql.GenSql (

         genSql
       , nameSubSql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
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

-- | generates a sql query from a RA query while creating a 
--   new name for subqueries and keeping the names that 
--   the user has used in their original query.
genSql :: RAlgebra -> SqlSelect
genSql = nameSubSql . transAlgebra2Sql 

-- | names subqueries within a sql query.
nameSubSql :: SqlSelect -> SqlSelect
nameSubSql (SqlSelect as ts cs) = SqlSelect as (nameRels ts) cs
nameSubSql q = q

-- | 
nameRels :: [SqlRelation] -> [SqlRelation]
nameRels = undefined

-- nameRel :: SqlRelation -> 