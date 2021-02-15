-- | generates sql queries from sql queries/ra queries
--   and renames subqueries/relations without an alias.
module VDBMS.QueryGen.Sql.GenSql (

         genSql
       , nameSubSql

) where 

-- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name 
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List ((\\))

import Control.Monad.State 

import Data.Maybe (isNothing, fromJust)

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
genSql :: Sql -> Sql
genSql = evalQState . nameSubSql 

-- TODO: attributes qualifiers must also be updated.
-- | names subqueries within a sql query.
nameSubSql :: Sql -> QState Sql
nameSubSql (Sql (SelectFromWhere as ts cs))
  = do ts' <- mapM nameRel ts
       return $ Sql (SelectFromWhere as ts' cs)
  -- = mapM nameRels ts >>= return (\ts' -> SqlSelect as ts' cs)
nameSubSql (SqlBin o lq rq) 
  = do lq' <- nameSubSql lq
       rq' <- nameSubSql rq 
       return $ SqlBin o lq' rq'
nameSubSql q = return q

-- | names a sql relation without a name.
-- nameRel :: [SqlAttrExpr] -> [SqlCond SqlSelect] -> Rename SqlRelation 
--         -> QState (Rename SqlRelation)
nameRel :: Rename SqlRelation -> QState (Rename SqlRelation)
-- nameRel = undefined
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
    = do if null (sqlattributes subq)
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
-- updateAttsQual :: SqlSelect -> SqlSelect
-- updateAttsQual (SqlSelect as ts cs) = undefined
--   -- = SqlSelect (map () as)
--   --             ts 
--   --             cs
-- updateAttsQual (SqlBin o l r) 
--   = SqlBin o (updateAttsQual l) (updateAttsQual r)
-- updateAttsQual q = q

-- -- | updates attribute's qualifer.
-- updateAttQual :: Attr -> Alias -> Attr
-- updateAttQual a n 
--   | isNothing (qualifier a) = a 
--   | not (isNothing n) = updateAttrQual a (SubqueryQualifier (fromJust n))
--   | otherwise = error "alias shouldn't be nothing"

-- -- |
-- updateQualsInCond :: SqlSelect -> SqlSelect
-- updateQualsInCond (SqlSelect as ts cs) = undefined
-- updateQualsInCond (SqlBin o l r) 
--   = SqlBin o (updateQualsInCond l) (updateQualsInCond r)
-- updateQualsInCond q = q

