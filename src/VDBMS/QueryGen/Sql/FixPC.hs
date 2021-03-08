-- | generates sql queries from sql queries/ra queries
--   and renames subqueries/relations without an alias.
module VDBMS.QueryGen.Sql.FixPC where 

-- -- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..))
-- import VDBMS.QueryLang.RelAlg.Relational.Algebra
-- -- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name 
-- -- import VDBMS.QueryLang.SQL.Condition 
-- -- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- -- import VDBMS.VDB.Schema.Variational.Schema

-- -- import Data.List ((\\))

-- import Control.Monad.State 

-- import Data.Maybe (isNothing, fromJust)

-- import Data.Map.Strict (Map)
-- import qualified Data.Map.Strict as SM

-- import Debug.Trace

-- |
fixPC :: Sql -> Sql 
fixPC (Sql sfw) = Sql $ fixPCsfw sfw
fixPC (SqlBin o l r) = SqlBin o (fixPC l) (fixPC r)
fixPC sql = sql  


-- |
fixPCsfw :: SelectFromWhere -> SelectFromWhere
fixPCsfw (SelectFromWhere as ts cs) = SelectFromWhere as' ts' cs
  where
    as' = undefined
    ts' = map fixPCrenameSqlRelation ts

-- |
fixPCrenameSqlRelation :: Rename SqlRelation -> Rename SqlRelation
fixPCrenameSqlRelation = undefined

