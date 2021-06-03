-- | injects the presence condition attached to a query
--   inside it.
module VDBMS.QueryGen.Sql.AddPC where 

-- -- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.QueryLang.SQL.Pure.Ops (deletePC)
-- import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..))
-- import VDBMS.QueryLang.RelAlg.Relational.Algebra
-- -- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name 
import VDBMS.Features.ConfFexp (conf2fexp)
import VDBMS.Features.Config 
import VDBMS.Features.FeatureExpr.FeatureExpr (Feature, FeatureExpr)
-- import VDBMS.VDB.GenName 
-- -- import VDBMS.QueryLang.SQL.Condition 
-- -- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- -- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List (delete)

-- import Control.Monad.State 

-- import Data.Maybe (isNothing, fromJust)

-- import Data.Map.Strict (Map)
-- import qualified Data.Map.Strict as SM

-- import Debug.Trace


-- |
addConf2PC :: PCatt -> [Feature] -> (Config Bool, Sql) -> Sql
addConf2PC pc fs (c,(Sql (SelectFromWhere as ts cs))) 
  = Sql (SelectFromWhere as' ts cs)
    where 
      as' = SqlAndPCFexp (Attr pc Nothing) (conf2fexp fs c) pc : as 
addConf2PC pc fs (c,(SqlBin o l r)) 
  = SqlBin o (addConf2PC pc fs (c,l)) (addConf2PC pc fs (c,r))
addConf2PC _ _ (_,q) = q

-- |
addFexp2PC :: PCatt -> (FeatureExpr, Sql) -> Sql
addFexp2PC pc (f,(Sql (SelectFromWhere as ts cs))) 
  = Sql (SelectFromWhere as' ts cs)
    where 
      as' = SqlAndPCFexp (Attr pc Nothing) f pc : as 
addFexp2PC pc (f,(SqlBin o l r)) 
  = SqlBin o (addFexp2PC pc (f,l)) (addFexp2PC pc (f,r))
addFexp2PC _ (_,q) = q

