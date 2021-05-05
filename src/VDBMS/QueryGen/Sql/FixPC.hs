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

-- | drops the pc attribute and instead conjuncts the 
--   pc of all attributes and renames it as pc.
fixPC :: PCatt -> Sql -> Sql 
fixPC pc q@(Sql sfw)      = 
  -- trace ("query is :" ++ show q) $
  Sql $ fixPCsfw pc sfw
fixPC pc (SqlBin o l r) = SqlBin o (fixPC pc l) (fixPC pc r)
fixPC _   sql           = sql  


-- | drops the pc attribute and instead conjuncts the 
--   pc of all attributes and renames it as pc.
fixPCsfw :: PCatt -> SelectFromWhere -> SelectFromWhere
fixPCsfw pc (SelectFromWhere as ts cs) 
  = SelectFromWhere (dropEmptyConcat as') ts' cs
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
      -- drops the empty concat of pc and replaces it with pc
      dropEmptyConcat :: [SqlAttrExpr] -> [SqlAttrExpr]
      dropEmptyConcat = map dropIt
        where 
          dropIt :: SqlAttrExpr -> SqlAttrExpr
          dropIt (SqlAndPCs [] pc) 
            = SqlAttr (Rename Nothing (Attr pc Nothing))
          dropIt a = a



-- | drops the pc attribute and instead conjuncts the 
--   pc of all attributes and renames it as pc.
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

-- | fixes the misplaced pc conjunct attribute: removes the conjunction
--   that has an empty list of attributes. it also moves the 
--   attribute expression one level up if the conjunction pc is 
--   the only attribute.
-- fixMisplacedPC :: PCatt -> SelectFromWhere -> SelectFromWhere
-- fixMisplacedPC pc sfw@(SelectFromWhere as ts cs) 
--   = SelectFromWhere as''' ts' cs
--     where
--       as' = dropEmptyPC as
--       (ts', as'') = fixMisplacedPCsubs ts 
--       as''' = addAttPCs2attExp pc as' as''

-- -- |
-- fixMisplacedPCsubs :: [Rename SqlRelation]
--                    -> ([Rename SqlRelation], [SqlAttrExpr])
-- fixMisplacedPCsubs rrs = undefined

-- -- | drops the sql att that has an empty list of pc.
-- dropEmptyPC :: [SqlAttrExpr] -> [SqlAttrExpr]
-- dropEmptyPC as = filter (not . isAndPCsEmpty) as  

-- -- | checks if and of pcs is the only sql att exp.
-- isPCOnlyAtt :: [SqlAttrExpr] -> Bool
-- isPCOnlyAtt as 
--   | length as == 1 = case (isAndPCs (head as)) of 
--     True  -> True
--     False -> False
--   | otherwise = False




