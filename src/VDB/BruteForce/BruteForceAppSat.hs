-- Applies the sat solver to the result of queries sent to the db
module VDB.BruteForce.BruteForceAppSat where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
import VDB.SAT
import VDB.BruteForce.BruteForceSendQs

import Data.SBV 
import Data.Maybe (catMaybes)

import Database.HDBC
import Database.HDBC.SqlValue

type Vctxt = F.FeatureExpr
type PresCondAttName = String

-- | updates the pres cond of a tuple based on the vctxt, if satisfiable 
--   returns the tuple with updated and shrinked pres cond, if not
--   returns nothing
--   one row returned by query -> name of pres cond attr -> vcontxt -> update the feature exp of tuple based on vctxt
checkSatRow :: ClmNameIncludedRow -> PresCondAttName -> Vctxt -> Maybe ClmNameIncludedRow
checkSatRow tuple p vctxt = case presCond of 
  Just pres -> case satisfiable comb of 
                 True -> Just $ map 
                         (\(clm,val) -> if clm == p 
                                        then (clm,F.fexp2sqlval (F.shrinkFeatureExpr comb))
                                        else (clm,val)) 
                         tuple
                 _ -> Nothing
                 where comb = F.And vctxt (F.sqlval2fexp pres)
  _ -> Nothing
  where presCond = lookup p tuple

-- | takes a table (i.e. a list of tuples), the attribute name of pres cond,
--   the current variational context and returns the filtered out table based
--   the variatinoal ctxt. note that the vctxt is coming from the vquery, i.e.
--   it's the feature exp attached to the query that is being executed on the
--   relational db
checkSatTable :: ClmNameIncludedTable -> PresCondAttName -> Vctxt -> ClmNameIncludedTable
checkSatTable t p vctxt = catMaybes (checkSatTableMaybe t p vctxt)


-- | auxilary function for checkSatTable
checkSatTableMaybe :: ClmNameIncludedTable -> PresCondAttName -> Vctxt -> [Maybe ClmNameIncludedRow]
checkSatTableMaybe t p vctxt = map ((flip4 checkSatRow) p vctxt) t

-- | aux func for checksattablemaybe
flip4 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip4 f b c a = f a b c

-- | takes a vtable (i.d. opt table) and checks for satisfiability of 
--   its pres cond with the vctxt, where again is coming from the vquery,
--   and returns maybe vtable, which is nothing if the satisfiability fails
--   so that we don't check satisfiability with tuples
--   MAY BE ABLE TO OPTIMIZE IT MORE!!!!!
checkSatVtablePresCond :: ClmNameIncludedVtable -> Vctxt -> Maybe ClmNameIncludedVtable
checkSatVtablePresCond (o,t) vctxt = case satisfiable comb of 
  True -> Just ((F.shrinkFeatureExpr comb), t)
  _ -> Nothing
  where 
    comb = F.And vctxt o


-- ** idea: check sat of pres of table first and then adjust it
--          then conjuct that with tuples so the vctxt becomes 
--          fexp attached to vquery conjucted with the pres cond of table


-- | takes a list of vtables and vctxt (coming from vqs) and 
--   applies the vctxt of each of them to the pres cond of vtable
--   it returns nothing if the `vctxt and pres cond` is unsatisfiable
checkSatVtablePresCondsMaybe :: [(ClmNameIncludedVtable, Vctxt)] -> [Maybe ClmNameIncludedVtable]
checkSatVtablePresCondsMaybe = map (uncurry checkSatVtablePresCond) 

-- | assuming that the pres cond of vtable is adjusted based on the
--   vctxt of vq, it applies it to the tuples of the vtable
checkSatVtableTuples :: ClmNameIncludedVtable -> PresCondAttName -> ClmNameIncludedVtable
checkSatVtableTuples (f,t) p = (f, checkSatTable t p f)

-- | does checksatvtabletuples over a list of vtables
checkSatVtablesTuples :: [ClmNameIncludedVtable] -> PresCondAttName -> [ClmNameIncludedVtable]
checkSatVtablesTuples vts p = map ((flip checkSatVtableTuples) p) vts

-- | drops the Nothings from checkSatVtablesMaybe result
checkSatVtablePresConds :: [(ClmNameIncludedVtable, Vctxt)] -> [ClmNameIncludedVtable]
checkSatVtablePresConds = catMaybes . checkSatVtablePresCondsMaybe 

-- | first applies the vctxt from vqs to vtables and adjusts vtable pres conds
--   then filters out tuples of vtables based on their satisfiability
--   with the new pres cond
checkSatAllVtables :: [(ClmNameIncludedVtable, Vctxt)] -> PresCondAttName -> [ClmNameIncludedVtable]
checkSatAllVtables vs p = checkSatVtablesTuples filteredVtablePresConds p
  where 
    filteredVtablePresConds = checkSatVtablePresConds vs


-- checkSatVtableMap :: ClmVtableMap -> ClmVtableMap
-- checkSatVtableMap = undefined

