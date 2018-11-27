-- Applies the sat solver to the result of queries sent to the db
module VDB.BruteForce.BruteForceAppSat where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
import VDB.SAT

import VDB.BruteForce.BruteForceSendQs
--import VDB.BruteForce.BruteForceAlg2Sql

-- import Data.Text 
-- as T (Text, pack, append, concat)
import Data.SBV 
import Data.Maybe (catMaybes)

import Database.HDBC
import Database.HDBC.SqlValue

type Vctxt = F.FeatureExpr
type PresCondAttName = String

-- type Row = [SqlValue]
-- type Table = [Row]
-- type Vtable = Opt Table

-- type ClmNameIncludedRow = [(String, SqlValue)]
-- type ClmNameIncludedTable = [ClmNameIncludedRow]
-- type ClmNameIncludedVtable = Opt ClmNameIncludedTable

-- type ClmRowMap = Map String SqlValue
-- type ClmTableMap = [ClmRowMap]
-- type ClmVtableMap = Opt ClmTableMap

-- type Query = T.Text
-- type Vquery = Opt Query


-- | updates the pres cond of a tuple based on the vctxt, if satisfiable 
--   returns the tuple with updated and shrinked pres cond, if not
--   returns nothing
--   one row returned by query -> name of pres cond attr -> vcontxt -> update the feature exp of tuple based on vctxt
checkSatClmRow :: ClmNameIncludedRow -> PresCondAttName -> Vctxt -> Maybe ClmNameIncludedRow
checkSatClmRow tuple p vctxt = case presCond of 
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

-- * concat maybes
-- * alternative 


-- | takes a table (i.e. a list of tuples), the attribute name of pres cond,
--   the current variational context and returns the filtered out table based
--   the variatinoal ctxt. note that the vctxt is coming from the vquery, i.e.
--   it's the feature exp attached to the query that is being executed on the
--   relational db
checkSatTable :: ClmNameIncludedTable -> PresCondAttName -> Vctxt -> ClmNameIncludedTable
checkSatTable t p vctxt = catMaybes (checkSatTableMaybe t p vctxt)


-- | auxilary function for checkSatTable
checkSatTableMaybe :: ClmNameIncludedTable -> PresCondAttName -> Vctxt -> [Maybe ClmNameIncludedRow]
checkSatTableMaybe t p vctxt = map ((flip4 checkSatClmRow) p vctxt) t

-- | aux func for checksatvtable 
flip4 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip4 f b c a = f a b c

-- | takes a vtable (i.d. opt table) and checks for satisfiability of 
--   its pres cond with the vctxt, where again is coming from the vquery,
--   and returns maybe vtable, which is nothing if the satisfiability fails
--   so that we don't check satisfiability with tuples
--   MAY BE ABLE TO OPTIMIZE IT MORE!!!!!
checkSatVtable :: ClmNameIncludedVtable -> Vctxt -> Maybe ClmNameIncludedVtable
checkSatVtable (o,t) vctxt = case satisfiable comb of 
  True -> Just ((F.shrinkFeatureExpr comb), t)
  _ -> Nothing
  where 
    comb = F.And vctxt o


-- ** idea: check sat of pres of table first and then adjust it
--          then conjuct that with tuples so the vctxt becomes 
--          fexp attached to vquery conjucted with the pres cond of table


-- | takes 
checkSatVtables :: [(ClmNameIncludedVtable, Vctxt)] -> [Maybe ClmNameIncludedVtable]
checkSatVtables = undefined


checkSatAllVtables :: [ClmNameIncludedVtable] -> PresCondAttName -> [ClmNameIncludedVtable]
checkSatAllVtables = undefined


-- checkSatVtableMap :: ClmVtableMap -> ClmVtableMap
-- checkSatVtableMap = undefined







