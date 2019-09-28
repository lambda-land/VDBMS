-- | generates sql queries from sql queries/ra queries
--   and renames subqueries/relations without an alias.
module VDBMS.QueryGen.Sql.GenSql (

         genSql
       , nameSubSql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name (Rename(..))
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List ((\\))

import Control.Monad.State 

-- | number for generating names.
type AliasNum = Int 

-- -- | A Query monad provides unique names (aliases)
-- --   and constructs a SqlSelect.
-- type QState = State AliasNum SqlSelect
type QState = State AliasNum 
-- data Query  = Query (QState -> QState)

-- | evaluates the qstate with zero.
evalQState :: QState a -> a
evalQState = flip evalState initState
  where initState = 0

-- | gives names to a subqueries and relations of a given
--   sql query.
genSql :: SqlSelect -> SqlSelect
genSql = evalQState . nameSubSql 

-- | names subqueries within a sql query.
nameSubSql :: SqlSelect -> QState SqlSelect
nameSubSql (SqlSelect as ts cs) 
  = do ts' <- mapM nameRel ts 
       return $ SqlSelect as ts' cs
  -- = mapM nameRels ts >>= return (\ts' -> SqlSelect as ts' cs)
nameSubSql (SqlBin o lq rq) 
  = do lq' <- nameSubSql lq
       rq' <- nameSubSql rq 
       return $ SqlBin o lq' rq'
nameSubSql q = return q

-- | names a sql relation without a name.
nameRel :: SqlRelation -> QState SqlRelation
nameRel q@(SqlSubQuery rq)
  = do q' <- nameSubSql (thing rq)
       s <- get 
       if name rq == Nothing
       then do s <- get
               let q'' = SqlSubQuery (Rename (Just ("t"++ show s)) (thing rq))
               modify succ
               return q''
       else return q
nameRel (SqlInnerJoin l r c) 
  = do l' <- nameRel l
       r' <- nameRel r
       return $ SqlInnerJoin l' r' c


