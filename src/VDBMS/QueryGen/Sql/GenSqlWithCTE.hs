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
genSqlCTE :: SqlSelect -> SqlSelect
genSqlCTE (SqlSelect as ts cs) = undefined
genSqlCTE (SqlBin o l r) = undefined
genSqlCTE q@(SqlTRef _) = q
genSqlCTE (SqlEmpty) = SqlEmpty


genCTEs :: SqlSelect -> [(String, SqlSelect)] -> CteState SqlTempRes
genCTEs = undefined
-- -- -- | A Query monad provides unique names (aliases)
-- -- --   and constructs a SqlSelect.
-- -- type QState = State AliasNum SqlSelect
-- type QState = State AliasNum 
-- -- data Query  = Query (QState -> QState)

-- -- | evaluates the qstate with zero.
-- evalQState :: QState a -> a
-- evalQState = flip evalState initState
--   where initState = 0

-- -- | generates a sql query from a RA query while creating a 
-- --   new name for subqueries and keeping the names that 
-- --   the user has used in their original query.
-- genSql :: RAlgebra -> SqlSelect
-- genSql q = evalQState (nameSubSql sql) 
--   where sql = transAlgebra2Sql q

-- -- | names subqueries within a sql query.
-- nameSubSql :: SqlSelect -> QState SqlSelect
-- nameSubSql (SqlSelect as ts cs) 
--   = do ts' <- mapM nameRel ts 
--        return $ SqlSelect as ts' cs
--   -- = mapM nameRels ts >>= return (\ts' -> SqlSelect as ts' cs)
-- nameSubSql (SqlBin o lq rq) 
--   = do lq' <- nameSubSql lq
--        rq' <- nameSubSql rq 
--        return $ SqlBin o lq' rq'
-- nameSubSql q = return q

-- -- | names a sql relation without a name.
-- nameRel :: SqlRelation -> QState SqlRelation
-- nameRel q@(SqlSubQuery rq)
--   = do q' <- nameSubSql (thing rq)
--        s <- get 
--        if name rq == Nothing
--        then do s <- get
--                let q'' = SqlSubQuery (Rename (Just ("t"++ show s)) (thing rq))
--                modify succ
--                return q''
--        else return q
-- nameRel (SqlInnerJoin l r c) 
--   = do l' <- nameRel l
--        r' <- nameRel r
--        return $ SqlInnerJoin l' r' c


