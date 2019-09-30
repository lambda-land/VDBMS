-- | generates sql queries with ctes given a sql query.
module VDBMS.QueryGen.Sql.GenSqlWithCTE (

         genCTEs

) where 

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
evalCteState :: CteState a -> a 
evalCteState = flip evalState initState
  where initState = 0

-- | generates sql queries with ctes given a sql query.
-- genSqlCTE :: SqlSelect -> SqlSelect
-- genSqlCTE (SqlSelect as ts cs) = undefined
-- genSqlCTE (SqlBin o l r) = undefined
-- genSqlCTE q@(SqlTRef _) = q
-- genSqlCTE (SqlEmpty) = SqlEmpty


-- genCTEs :: SqlSelect -> CteClosure -> CteState SqlTempRes
genCTEs :: MonadState s m => SqlSelect -> CteClosure -> m SqlTempRes
genCTEs (SqlSelect as ts cs) cls = undefined
  -- = do n <- M.lookup 
    -- for every t in ts do:
    -- look up sql rel in closure
    -- if not exist add it
    -- if exists replace it with its name
    -- look into atts and conds to see if you're using the name if sqlrel, 
      -- if so substitute the name
    -- move to the next t
genCTEs (SqlBin o l r) cls = undefined
genCTEs (SqlTRef r) cls = undefined
genCTEs SqlEmpty cls = undefined


cteCheck :: MonadState s m => SqlSelect -> CteClosure -> CteState SqlSelect
         -> SqlRelation -> m SqlTempRes
cteCheck q cls s (SqlSubQuery rq) = undefined
  -- = do num <- get 
  --      let n = M.lookup (thing rq) cls 
  --      if isNothing n
  --      then do let name = "temp" ++ show num
  --                  cls' = M.insert (thing rq) name cls
  --              modify succ
  --      else do name <- n 
  --              return name 
  --      return ()
cteCheck q cls s (SqlInnerJoin l r c) = undefined
  -- = do 

-- | ??
-- checkSqlRel :: SqlRelation -> CteClosure 

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







