-- | generates sql queries with ctes given a sql query.
module VDBMS.QueryGen.Sql.GenSqlWithCTE where 

-- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name (Rename(..), Name)
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

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
-- evalCteState :: CteState a -> a 
-- evalCteState = flip evalState initState
--   where initState = 0

-- | takes a sql select query and generates the initial sql temp res.
initCTE :: SqlSelect -> SqlTempRes
initCTE q@(SqlSelect _ _ _) = SqlCTE M.empty q
initCTE q@(SqlBin _ _ _)    = SqlCTE M.empty q
initCTE q@(SqlTRef _)       = SqlCTE M.empty q
initCTE SqlEmpty            = SqlCTE M.empty SqlEmpty 

-- | updates a sql temp res one relation at the time.
updateCTE :: MonadState s m => SqlTempRes -> m SqlTempRes
updateCTE cte = 
  case query cte of 
    (SqlSelect as ts cs) -> return cte
    (SqlBin o l r) -> return cte
    q -> return cte

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


-- | update attribute expressions.
updateAtts :: Name -> [SqlAttrExpr] -> [SqlAttrExpr]
updateAtts = undefined

-- | update relational condition.
updateRCond :: Name -> Name -> RCondition -> RCondition
updateRCond l r c = undefined

-- | update conditions.
updateConds :: Name -> [SqlCond SqlSelect] -> [SqlCond SqlSelect]
updateConds = undefined

-- | update sql select query.
updateSqlQuery :: SqlRelation -> Name -> SqlSelect -> SqlSelect
updateSqlQuery r n (SqlSelect as ts cs) = undefined
updateSqlQuery _ _ _ = error "only accept sqlselct constructor"







