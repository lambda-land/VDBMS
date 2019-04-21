-- | checks the validity of opt vqs, 1) fexp is send to sat solver
--   2) the type system checks the query
--   and returns the valid opt vq with shrinked fexp and and table sch.
-- TODO: apply the relaitonal optimizer here too!
module VDB.QueryTrans.OptVqToOptVqTblSch where 

import VDB.Algebra
-- import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import VDB.TypeSystem
import VDB.Schema

-- 
validOptQs :: [Opt Algebra] -> [Opt (Algebra,TableSchema)]
validOptQs oqs = undefined
  -- where
  --   filteredOqs = filter 

