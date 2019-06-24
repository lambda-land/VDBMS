-- | Sql VTable. the pres cond of the sqltable has been converted to 
--   a feature expresion.
module VDBMS.DBMS.Table.SqlVtable (

        SqlVtable,
        VTuple,
        VTuples,
        disjoinDuplicate,
        constVTuple,
        constVTuples,
        destVTuple,
        destVTuples

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.List (deleteBy,groupBy)

import VDBMS.Variational.Opt 
import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Schema.Schema
import VDBMS.DBMS.Value.Value
import VDBMS.Features.SAT 
import VDBMS.DBMS.Table.Table

type SqlVtable = Opt SqlTable

type VTuple = Opt SqlRow
type VTuples = [VTuple]


-- | removes tuples that have the same values except for pres
--   cond, inserts only one such tuple and disjuncts all 
--   their pres conds.
-- NOTE: time this separately!!
disjoinDuplicate :: PresCondAtt -> SqlTable -> SqlTable
disjoinDuplicate p t = destVTuples p shrinkedFexpRes
-- destVTuples p resTs -- just disjoins duplicate tuples
-- destVTuples p dropFalseRowsRes -- also drops tuples with false fexp
-- destVTuples p shrinkedFexpRes-- also shrinks fexp of tuples
  where
    vtuples :: VTuples
    vtuples = constVTuples p t 
    groupedTs :: [VTuples]
    groupedTs = groupBy (\x y -> snd x == snd y) vtuples
    groupedFexpTs :: [([FeatureExpr],SqlRow)]
    groupedFexpTs = map pushDownList groupedTs
    mapFst g (a,b) = (g a,b)
    resTs = map (mapFst disjFexp) groupedFexpTs
    dropFalseRowsRes = filter (satisfiable . fst) resTs
    shrinkedFexpRes = map (mapFst shrinkFeatureExpr) dropFalseRowsRes


-- | constructs a list of fexp for the group of vtuples
--   that have the same tuple.
--   NOTE: this is unsafe since you're not checking if 
--         the first element of pairs are the same!
pushDownList :: [(a,b)] -> ([a],b)
pushDownList [(a,b)] = ([a],b)
pushDownList ((a,b):l) = (a:fst (pushDownList l),b)

-- | extract the pres cond out of sqlrow and attachs it
--   as the presence condition to the tuple.
constVTuple :: PresCondAtt -> SqlRow -> VTuple
constVTuple p r = mkOpt f t 
  where 
    pName = presCondAttName p
    f = case M.lookup pName r of
          Just v -> sqlval2fexp v
          _      -> Lit False
    t = M.delete pName r

-- | constructs a table of vtuples.
constVTuples :: PresCondAtt -> SqlTable -> VTuples
constVTuples p t = map (constVTuple p) t

-- | destructs a vtuple into a sqlrow.
destVTuple :: PresCondAtt -> VTuple -> SqlRow
destVTuple p t = M.insert (presCondAttName p) (fexp2sqlval $ getFexp t) $ getObj t

-- | destructs a vtuples into a sqltable.
destVTuples :: PresCondAtt -> VTuples -> SqlTable
destVTuples p ts = map (destVTuple p) ts 


