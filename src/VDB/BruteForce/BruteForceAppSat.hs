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

import VDB.BruteForce.BruteForceSendQs
--import VDB.BruteForce.BruteForceAlg2Sql

--import Data.Text as T (Text, pack, append, concat)
import Data.SBV 

import Database.HDBC
import Database.HDBC.SqlValue

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


checkSatClmRow :: ClmNameIncludedRow -> F.FeatureExpr -> ClmNameIncludedRow
checkSatClmRow = undefined

checkSatVtable :: ClmNameIncludedVtable -> ClmNameIncludedVtable
checkSatVtable = undefined 


checkSatVtableMap :: ClmVtableMap -> ClmVtableMap
checkSatVtableMap = undefined