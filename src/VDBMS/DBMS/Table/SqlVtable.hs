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
        destVTuples,
        applyFexpToSqlVtable,
        updateTuplesPCInSqlVtable
        , prettySqlVTable

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.List (groupBy)
import Data.Maybe (fromJust)

import VDBMS.Variational.Opt 
import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.Features.SAT 
import VDBMS.DBMS.Table.Table

type SqlVtable = Opt SqlTable 
-- type SqlVtable = Opt VTuples

-- | pretty prints a sql vtable
prettySqlVTable :: [Attribute] -> SqlVtable -> String
prettySqlVTable as t
  = show (getFexp t)
  ++ "\n"
  ++ prettySqlTable as (getObj t)

type VTuple = Opt SqlRow
type VTuples = [VTuple]

-- | applies a feature expression to tuples of a sqlvtable and
--   drops the ones that are not valid, i.e., their pc is not
--   satisfiable.
applyFexpToSqlVtable :: FeatureExpr -> PCatt -> SqlVtable -> SqlVtable
applyFexpToSqlVtable f pc t 
  | isTableNull (getObj t) = updateOptObj [] t
  | otherwise = applyFuncObj (filter (satisfiable . tuple_pc)) t
  where 
    pcName = attributeName pc
    t_pc = getFexp t
    -- tab = getObj t
    tuple_pc tuple 
      = And (And f t_pc) ((sqlval2fexp . fromJust) $ M.lookup pcName tuple)

-- | updates tuples pc in a sqlvarianttable to the fexp of the conf.
updateTuplesPCInSqlVtable :: PCatt -> SqlVtable -> SqlTable
updateTuplesPCInSqlVtable pc t = updatePCInSqlTable pc (getFexp t) (getObj t)

-- | removes tuples that have the same values except for pres
--   cond, inserts only one such tuple and disjuncts all 
--   their pres conds.
-- NOTE: time this separately!!
disjoinDuplicate :: PCatt -> SqlTable -> SqlTable
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
    mapFst' g (a,b) = (g a,b)
    resTs = map (mapFst' disjFexp) groupedFexpTs
    dropFalseRowsRes = filter (satisfiable . fst) resTs
    shrinkedFexpRes = map (mapFst' shrinkFExp) dropFalseRowsRes


-- | constructs a list of fexp for the group of vtuples
--   that have the same tuple.
--   NOTE: this is unsafe since you're not checking if 
--         the first element of pairs are the same!
pushDownList :: [(a,b)] -> ([a],b)
pushDownList [(a,b)] = ([a],b)
pushDownList ((a,b):l) = (a:fst (pushDownList l),b)
pushDownList [] = error "wasn't expecting an empty list!!"

-- | extract the pres cond out of sqlrow and attachs it
--   as the presence condition to the tuple.
constVTuple :: PCatt -> SqlRow -> VTuple
constVTuple p r = mkOpt f t 
  where 
    pName = presCondAttName p
    f = case M.lookup pName r of
          Just v -> sqlval2fexp v
          _      -> Lit False
    t = M.delete pName r

-- | constructs a table of vtuples.
constVTuples :: PCatt -> SqlTable -> VTuples
constVTuples p t = map (constVTuple p) t

-- | destructs a vtuple into a sqlrow.
destVTuple :: PCatt -> VTuple -> SqlRow
destVTuple p t = M.insert (presCondAttName p) (fexp2sqlval $ getFexp t) $ getObj t

-- | destructs a vtuples into a sqltable.
destVTuples :: PCatt -> VTuples -> SqlTable
destVTuples p ts = map (destVTuple p) ts 


