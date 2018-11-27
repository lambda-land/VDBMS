-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BuildVres where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
--import VDB.DBsetup.EnronEmailDB

import Data.Map

--import Database.HDBC.Sqlite3
import Database.HDBC

