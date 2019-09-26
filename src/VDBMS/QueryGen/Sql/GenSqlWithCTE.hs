-- | generates sql queries with ctes given a sql query.
module VDBMS.QueryGen.Sql.GenSqlWithCTE (

         genSqlCTE

) where 

-- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
-- import VDBMS.VDB.Name (Rename(..))
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List ((\\))

-- import Control.Monad.State 

-- | generates sql queries with ctes given a sql query.
genSqlCTE :: SqlSelect -> SqlSelect
genSqlCTE = undefined