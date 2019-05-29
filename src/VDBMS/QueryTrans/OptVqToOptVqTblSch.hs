-- | checks the validity of opt vqs, 1) fexp is send to sat solver
--   2) the type system checks the query
--   and returns the valid opt vq with shrinked fexp and and table sch.
-- TODO: apply the relaitonal optimizer here too!
module VDBMS.QueryTrans.OptVqToOptVqTblSch where 

import VDBMS.QueryLang.Variational.Algebra
-- import VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import qualified VDB.Condition as C
import VDBMS.Variational.Opt
import VDBMS.TypeSystem.TypeSystem
import VDBMS.VDB.Schema.Schema
import VDBMS.Features.SAT 

import Control.Arrow

-- | applies the function f to elements of the list
--   and filters out the ones that return Nothing.
filterMaybes :: (Opt a -> Maybe b) -> [Opt a] -> [Opt a]
filterMaybes f os = [a | (a, Just b) <- os']
  where
    os' = zip os $ fmap f os



-- 
validOptQs :: [Opt Algebra] -> Schema 
  -> [Opt (Algebra, TableSchema)]
validOptQs oqs s = catMaybees oqts
  where
    filteredOqs = filter (\(o,_) -> satisfiable o) oqs
    shrinkedOqs = fmap (first F.shrinkFeatureExpr) filteredOqs
    qt oq = updateOptObj (getObj oq,typeOfVquery' (getObj oq) (getFexp oq) s) oq
    oqts = fmap qt shrinkedOqs
    catMaybees [] = []
    catMaybees (x:xs) = case snd (getObj x) of 
                          Just t -> updateOptObj (fst (getObj x), t) x : catMaybees xs
                          _ -> catMaybees xs

-- checks for the validity of opt queries and gives back the ones that are
-- valid. Note that it doesn't return the table schema anymore!
checkValidityOptQs :: [Opt Algebra] -> Schema 
  -> [Opt Algebra]
checkValidityOptQs oqs s = filterMaybes (filterFunc) shrinkedOqs
  where
    filteredOqs = filter (\(o,_) -> satisfiable o) oqs
    shrinkedOqs = fmap (first F.shrinkFeatureExpr) filteredOqs
    filterFunc oq = typeOfVquery' (getObj oq) (getFexp oq) s

    


