-- | generates sql queries from sql queries/ra queries
--   and renames subqueries/relations without an alias.
module VDBMS.QueryGen.Sql.FixPC where 

-- -- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.QueryLang.SQL.Pure.Ops (deletePC)
-- import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..))
-- import VDBMS.QueryLang.RelAlg.Relational.Algebra
-- -- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name 
-- import VDBMS.VDB.GenName 
-- -- import VDBMS.QueryLang.SQL.Condition 
-- -- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- -- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List (delete)

-- import Control.Monad.State 

import Data.Maybe (isNothing, fromJust)

-- import Data.Map.Strict (Map)
-- import qualified Data.Map.Strict as SM

import Debug.Trace

-- |
fixPC :: PCatt -> Sql -> Sql 
fixPC pc (Sql sfw)      = Sql $ fixPCsfw pc sfw
fixPC pc (SqlBin o l r) = SqlBin o (fixPC pc l) (fixPC pc r)
fixPC _   sql           = sql  


-- |
fixPCsfw :: PCatt -> SelectFromWhere -> SelectFromWhere
fixPCsfw pc (SelectFromWhere as ts cs) = SelectFromWhere as' ts' cs
  where
    as' = deletePC as pc ++ [SqlAndPCs pcs pc]
    pcs = map (\q -> Attr pc (Just (SubqueryQualifier q))) 
              (concatMap getQual ts)
    getQual :: Rename SqlRelation -> [Name]
    getQual (Rename (Just alias) (SqlSubQuery _)) 
      = [alias]
    getQual (Rename Nothing (SqlSubQuery sql)) 
      -- = trace (show sql) $
      =  []
      -- = error "FixPC. fixPCsfw. shouldnt be in this case!!!"
    getQual (Rename Nothing (SqlInnerJoin lsr rsr _)) 
      = case (isNothing nlsr, isNothing nrsr) of
        (True,  True)  -> getQual lsr ++ getQual rsr
        (True,  False) -> getQual lsr ++ [fromJust nrsr]
        (False, True)  -> [fromJust nlsr] ++ getQual rsr
        (False, False) -> [fromJust nlsr, fromJust nrsr]
        where
          nlsr = name lsr
          nrsr = name rsr
    getQual (Rename _ (SqlInnerJoin _ _ _)) 
      = error "FixPC. fixPCsfw. shouldnt be in this case"
      -- | isNothing (name lsr) && isNothing (name rsr) 
      --   = getQual lsr ++ getQual rsr
      -- | isNothing (name lsr) && isNothing (name rsr) 
    ts' = map (fixPCrenameSqlRelation pc) ts

-- |
fixPCrenameSqlRelation :: PCatt -> Rename SqlRelation -> Rename SqlRelation
fixPCrenameSqlRelation pc (Rename a (SqlSubQuery sql)) 
  = Rename a (SqlSubQuery $ fixPC pc sql)
-- fixPCrenameSqlRelation _ q@(Rename Nothing (SqlSubQuery _)) 
--   = q --TODO
  -- = error "FixPC. fixPCrenameSqlRelation. shouldnt be in this case"
fixPCrenameSqlRelation pc (Rename a (SqlInnerJoin l r c))
  = Rename a (SqlInnerJoin (fixPCrenameSqlRelation pc l)
                           (fixPCrenameSqlRelation pc r)
                           c)

-- |
fixMisplacedPC :: SelectFromWhere -> SelectFromWhere
fixMisplacedPC sfw = undefined

-- |
dropEmptyPC :: [SqlAttrExpr] -> [SqlAttrExpr]
dropEmptyPC as = filter (not . isAndPCsEmpty) as  

-- |
isPCOnlyAtt :: [SqlAttrExpr] -> Bool
isPCOnlyAtt as 
  | length as == 1 = case (isAndPCs (head as)) of 
    True  -> True
    False -> False
  | otherwise = False




