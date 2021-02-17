-- | generates sql queries with ctes given a sql query.
-- Incomplete for now. After experiments if subqueries have 
-- been used a lot in a query, I'll implement this.
-- The theory is sitting on my desk though.
module VDBMS.QueryGen.Sql.GenSqlWithCTE (

       evalCteState
       , genCTE

) where 

-- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name 
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..))
-- import Data.List ((\\))

import Data.Maybe (isNothing)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Monad.State 

-- | number of generated cte.
type CteNum = Int

-- | cte state. 
type CteState = State CteNum

-- | evaluates a cte state with zero.
evalCteState :: CteState a -> a 
evalCteState = flip evalState initState
  where initState = 0

-- | generates the cte for a sql query.
genCTE :: Sql -> CteState SqlTempRes
genCTE = updateCTE . initCTE

-- | takes a sql select query and generates the initial sql temp res.
initCTE :: Sql -> SqlTempRes
initCTE = undefined
-- initCTE q@(SqlSelect _ _ _) = SqlCTE M.empty q
-- initCTE q@(SqlBin _ _ _)    = SqlCTE M.empty q
-- -- initCTE q@(SqlTRef _)       = SqlCTE M.empty q -- should never get to this!!
-- initCTE SqlEmpty            = SqlCTE M.empty SqlEmpty 

-- | updates a sql temp res one relation at the time.
updateCTE :: SqlTempRes -> CteState SqlTempRes
updateCTE = undefined
-- updateCTE (SqlCTE cls (SqlSelect as ts cs)) = undefined
--   -- | null ts = error "sql select should have relations in from clause!!"
--   -- | otherwise = updateRels cls as ts cs 
-- updateCTE (SqlCTE cls (SqlBin o q1 q2)) 
--   = case (isQueryInCls q1 cls, isQueryInCls q2 cls) of 
--       (Just t1, Just t2) -> return $ SqlCTE cls (SqlBin o (sqlRel t1) (sqlRel t2))
--       (Just t1, Nothing) -> 
--         do cte2 <- updateCTE (SqlCTE cls q2)
--            return $ SqlCTE (closure cte2) (SqlBin o (sqlRel t1) (query cte2))
--       (Nothing, Just t2) -> 
--         do cte1 <- updateCTE (SqlCTE cls q1)
--            return $ SqlCTE (closure cte1) (SqlBin o (query cte1) (sqlRel t2))
--       (Nothing, Nothing) -> 
--         do cte1 <- updateCTE (SqlCTE cls q1)
--            cte2 <- updateCTE (SqlCTE (closure cte1) q2)
--            return $ SqlCTE (closure cte2) (SqlBin o (query cte1) (query cte2))
-- -- updateCTE cte@(SqlCTE _ (SqlTRef _)) = return cte -- should never get here!!
-- updateCTE cte@(SqlCTE _ SqlEmpty) = return cte 
-- -- updateCTE cte = 
-- --   let cls = closure cte in 
-- --   case query cte of 
-- --     (SqlSelect as ts cs) ->
-- --       case length ts == 1 of 
-- --         True -> 
-- --           -- you may need to update atts conds and tables (check the closure and see if you need 
-- --           -- to update the names and remove a query written before!)
-- --           return cte
-- --           -- do num <- get 
-- --           --    let t = SqlSubQuery (Rename Nothing (SqlTRef (Relation ("temp" ++ show num))))
-- --           --    return $ SqlCTE cls (SqlSelect as [t] cs)
-- --         False -> 
-- --           do let t = head ts
-- --              case t of 
-- --                (SqlSubQuery rq) -> 
-- --                  do queryInClosure
-- --                     (cls', (as', cs')) <- updateSqlRel rq cls as cs 
-- --                     updateCTE $ SqlCTE cls' (SqlSelect as' (tail ts) cs')
-- --                (SqlInnerJoin l r c) ->
-- --                  do (lcls, (as', cs'), c') <- updateJoinRel l cls c as cs
-- --                     (rcls, (as'', cs''), c'') <- updateJoinRel r (getClosure lcls) c as' cs'
-- --                     let cls' = addJoinToCls (getThing lcls) (getThing rcls) c'' (getClosure rcls)
-- --                     updateCTE $ SqlCTE cls' (SqlSelect as'' (tail ts) cs'')
-- --     (SqlBin o l r) -> 
-- --       do cte' <- updateCTE (SqlCTE cls l)
-- --          cte'' <- updateCTE (SqlCTE (closure cte') r)
-- --          return $ SqlCTE (closure cte'') (SqlBin o (query cte') (query cte''))
-- --     q -> return cte

-- |
-- updateRels :: CteClosure -> [SqlAttrExpr] -> [SqlRelation] -> [SqlCond SqlSelect]
--            -> 

-- |
isQueryInCls :: Sql -> CteClosure -> Maybe Name 
isQueryInCls = undefined

-- |
isSqlRelInCls :: SqlRelation -> CteClosure -> Maybe Name
isSqlRelInCls = undefined

-- |
sqlRel :: Name -> Sql
sqlRel = undefined
-- = SqlTRef . Relation

-- | update a sql rel.
-- gets a rename q. checks to see if it exists in closure.
-- if yes gets the name assigned to it. updates atts and conds w.r.t. name from closure
--   instead of the name from rename q.
-- otherwise, it increments state, adds rename q to closure, updates atts and conds.
updateSqlRel :: Rename Sql -> CteClosure -> [SqlAttrExpr] -> [SqlCond Sql]
             -> CteState (CteClosure, ([SqlAttrExpr], [SqlCond Sql]))
updateSqlRel rq cls as cs = undefined
  -- = do let q = thing rq
  --          mn = name rq
  --          temp = SqlTempRes cls q
  --      cte <- updateCTE temp
  --      let q' = query cte 
  --          cls' = closure cte
  --      case mn of 
  --        (Just n) -> 
  --          M.lookup 
  --        Nothing -> 

-- | update attribute expressions.
updateAtts :: Name -> [SqlAttrExpr] -> [SqlAttrExpr]
updateAtts = undefined

-- | update relational condition.
updateRCond :: Name -> Name -> RCondition -> RCondition
updateRCond l r c = undefined

-- | update conditions.
updateConds :: Name -> [SqlCond Sql] -> [SqlCond Sql]
updateConds = undefined 

-- | adds a join to closure. 
addJoinToCls :: SqlRelation -> SqlRelation -> RCondition -> CteClosure -> CteClosure
addJoinToCls = undefined


-- | update relation from a join.
-- updates rcondition.
-- update sql query within sqlrel. --> why do I need this????
-- update att list.
-- update cond list.
updateJoinRel :: SqlRelation -> CteClosure -> RCondition 
             -> [SqlAttrExpr] -> [SqlCond Sql]
             -> CteState (AddClosure SqlRelation, ([SqlAttrExpr], [SqlCond Sql]), RCondition)
updateJoinRel = undefined
-- r n (SqlSelect as ts cs) = undefined
-- updateSqlRel _ _ _ = error "only accept sqlselct constructor"


-- genCTEs :: SqlSelect -> CteClosure -> CteState SqlTempRes
-- genCTEs :: MonadState s m => SqlSelect -> CteClosure -> m SqlTempRes
-- genCTEs q@(SqlSelect as ts cs) cls = undefined
--   -- = do mapM (updateSqlSelect q cls state?) ts
--     -- for every t in ts do:
--     -- look up sql rel in closure
--     -- if not exist add it
--     -- if exists replace it with its name
--     -- look into atts and conds to see if you're using the name if sqlrel, 
--       -- if so substitute the name
--     -- move to the next t
-- genCTEs (SqlBin o l r) cls 
--   = do lq <- genCTEs l cls 
--        let cls' = closure lq
--        rq <- genCTEs r cls'
--        return $ SqlCTE (closure rq) (SqlBin o (query lq) (query rq))
-- genCTEs q@(SqlTRef r) cls = return $ SqlCTE cls q
-- genCTEs    SqlEmpty   cls = return $ SqlCTE cls SqlEmpty


-- updateSqlTemp :: MonadState s m 
--          => SqlTempRes 
--          -> m SqlTempRes
-- updateSqlTemp (SqlCTE cls (SqlSelect as ts cs))
--   = do let t = head ts

--   = do num <- get 
--        let n = M.lookup (thing rq) cls 
--        if isNothing n
--        then do let name = "temp" ++ show num 
--                    cls' = M.insert (thing rq) name cls 
--                modify succ
--        else ?
--        let as' = updateAtts name as 
--            cs' = updateConds name cs 
--        return $ SqlCTE cls' (SqlSelect as' (tail ts) cs')
-- updateSqlSelect (SqlSelect as ts cs) cls (SqlInnerJoin l r c) = undefined
-- updateSqlSelect _ _ _ = error "expected sql select constructor!"

-- cteCheck q cls s (SqlSubQuery rq) = undefined
--   -- = do num <- get 
--   --      let n = M.lookup (thing rq) cls 
--   --      if isNothing n
--   --      then do let name = "temp" ++ show num
--   --                  cls' = M.insert (thing rq) name cls
--   --              modify succ
--   --      else do name <- n 
--   --              return name 
--   --      return ()
-- cteCheck q cls s (SqlInnerJoin l r c) = undefined
  -- = do 

-- | ??
-- checkSqlRel :: CteClosure -> CteState -> SqlRelation -> 
-- checkSqlRel cls (SqlSubQuery rq) = undefined
--   -- = do 
-- checkSqlRel cls (SqlInnerJoin l r c) = undefined


