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

import Control.Monad.State 

-- | number of generated cte.
type CteNum = Int

-- | cte state. 
type CteState = State CteNum

-- | evaluates a cte state with zero.
evalCteState :: CteState a -> a 
evalCteState = flip evalState initState
  where initState = 0

-- | generates sql queries with ctes given a sql query.
-- genSqlCTE :: SqlSelect -> SqlSelect
-- genSqlCTE (SqlSelect as ts cs) = undefined
-- genSqlCTE (SqlBin o l r) = undefined
-- genSqlCTE q@(SqlTRef _) = q
-- genSqlCTE (SqlEmpty) = SqlEmpty


genCTEs :: SqlSelect -> CteClosure -> CteState SqlTempRes
genCTEs (SqlSelect as ts cs) cls = undefined
genCTEs (SqlBin o l r) cls = undefined
genCTEs (SqlTRef r) cls = undefined
genCTEs SqlEmpty cls = undefined
