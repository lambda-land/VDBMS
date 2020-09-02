-- | generates sql queries from sql queries/ra queries
--   and renames subqueries/relations without an alias.
module VDBMS.QueryGen.Sql.GenSql (

         genSql
       , nameSubSql

) where 

-- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name (Rename(..))
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List ((\\))

import Control.Monad.State 

import Data.Maybe (isNothing)

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

-- TODO: attributes qualifiers must also be updated.
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
nameRel :: Rename SqlRelation -> QState (Rename SqlRelation)
-- nameRel rq@(Rename a q@(SqlTRef _)) 
--   | isNothing a 
--     = do s <- get
--          let rq' = Rename (Just ("t" ++ show s)) q
--          modify succ
--          -- put s
--          return rq'
--   | otherwise = return rq
nameRel rq@(Rename a q@(SqlSubQuery subq)) 
  | isNothing a && isrel subq
    = do subq' <- nameSubSql subq
         s <- get
         let rq' = Rename (Just ("t" ++ show s)) (SqlSubQuery subq')
         modify succ
         return rq'
  | isNothing a && issqlslct subq 
    = do if null (attributes subq)
            then return rq
            else do subq' <- nameSubSql subq
                    s <- get
                    let rq' = Rename (Just ("t" ++ show s)) (SqlSubQuery subq')
                    modify succ
                    return rq'
  | otherwise = return rq
-- TODO: we may need to updates condition for attributes qualifiers.
nameRel rq@(Rename a (SqlInnerJoin l r c)) 
  | isNothing a 
    = do l' <- nameRel l
         r' <- nameRel r 
         return $ Rename Nothing (SqlInnerJoin l' r' c)
  | otherwise = error "an inner join shouldn't have a name"
    where
      la = name l 
      ra = name r

-- |
updateAttQual :: SqlSelect -> SqlSelect
updateAttQual (SqlSelect as ts cs) = undefined
updateAttQual (SqlBin o l r) 
  = SqlBin o (updateAttQual l) (updateAttQual r)
updateAttQual q = q

-- |
updateQualsInCond :: SqlSelect -> SqlSelect
updateQualsInCond (SqlSelect as ts cs) = undefined
updateQualsInCond (SqlBin o l r) 
  = SqlBin o (updateQualsInCond l) (updateQualsInCond r)
updateQualsInCond q = q

