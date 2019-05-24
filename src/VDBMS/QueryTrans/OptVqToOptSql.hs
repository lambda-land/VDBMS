-- | checks the validity of opt vqs, 1) fexp is send to sat solver
--   2) the type system checks the query
--   and returns the valid opt vq with shrinked fexp and and table sch.
-- TODO: apply the relaitonal optimizer here too!
module VDBMS.QueryTrans.OptVqToOptSql where 

import qualified VDBMS.QueryLang.Algebra as A
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr as F
import qualified VDBMS.QueryLang.Condition as C
import VDBMS.Features.Variational
import VDBMS.TypeSystem
import VDBMS.VDB.Schema
import VDBMS.Features.SAT 

-- import qualified Database.HaskellDB as HSDB
import qualified Database.HaskellDB.PrimQuery as P

attListHSDB :: [Opt Attribute] -> P.Assoc 
attListHSDB = undefined

transCond2SqlCond :: C.Condition -> P.PrimExpr
transCond2SqlCond (C.Lit b) = 
  P.ConstExpr $ P.BoolLit b
transCond2SqlCond (C.Comp c al ar) = undefined
transCond2SqlCond (C.Not c) = 
  P.UnExpr P.OpNot $ transCond2SqlCond c
transCond2SqlCond (C.Or cl cr) = 
  P.BinExpr P.OpOr (transCond2SqlCond cl) (transCond2SqlCond cr)
transCond2SqlCond (C.And cl cr) =  
  P.BinExpr P.OpAnd (transCond2SqlCond cl) (transCond2SqlCond cr)
transCond2SqlCond (C.CChc _ _ _) = error "didn't expect to get get condition choices!!"



transAlgebra2Sql :: A.Algebra -> Schema -> P.PrimQuery
transAlgebra2Sql (A.SetOp o lq rq) s = P.Binary o' lsql rsql
  where
    lsql = transAlgebra2Sql lq s 
    rsql = transAlgebra2Sql rq s
    o' = case o of
           A.Union -> P.Union
           A.Diff -> P.Difference
           A.Prod -> P.Times
transAlgebra2Sql (A.Proj as q) s = P.Project assoc sql
  where
    sql = transAlgebra2Sql q s 
    assoc = attListHSDB as
transAlgebra2Sql (A.Sel c q) s = P.Restrict c' sql
  where
    sql = transAlgebra2Sql q s
    c' = transCond2SqlCond c
transAlgebra2Sql (A.AChc _ _ _) _ = error "didn't expect to get query choices here!!"
transAlgebra2Sql (A.TRef r) s = case scheme of 
  Just sch -> P.BaseTable (relationName r) $ fmap attributeName sch
  _ -> error $ "the relation " ++ (relationName r) ++ " deons't exist in the db!!"
  where
    scheme = lookupRelAttsList r s
transAlgebra2Sql A.Empty _ = P.Empty


