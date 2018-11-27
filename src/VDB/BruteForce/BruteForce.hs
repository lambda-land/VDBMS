-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BruteForce.BruteForce where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
import VDB.BruteForce.BruteForceAlg2Sql
import VDB.BruteForce.BruteForceAppSat
import VDB.BruteForce.BruteForceSendQs
--import VDB.DBsetup.EnronEmailDB

import Data.Map

--import Database.HDBC.Sqlite3
import Database.HDBC

-- steps of brute force approach:
-- 1. initialize vctxt to the pres cond of vsch
-- 2. translate the vq to sql qs *bruteTrans*
-- 3. get conn to db and run *runBruteQsClm* to run sql qs from trans 
-- 4. apply sat solver to vtables *checkSatAllVtables*
-- 5. show results as one vtable