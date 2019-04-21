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
import VDB.SAT 

import Control.Arrow

-- 
validOptQs :: [Opt Algebra] -> Schema 
  -> [Opt (Algebra, TableSchema)]
validOptQs oqs s = catMaybees oqts
  where
    filteredOqs = filter (\(o,q) -> satisfiable o) oqs
    shrinkedOqs = fmap (first F.shrinkFeatureExpr) filteredOqs
    qt oq = updateOptObj (getObj oq,typeOfVquery' (getObj oq) (getFexp oq) s) oq
    oqts = fmap qt shrinkedOqs
    catMaybees [] = []
    catMaybees (x:xs) = case snd (getObj x) of 
                          Just t -> updateOptObj (fst (getObj x), t) x : catMaybees xs
                          otherwise -> catMaybees xs

