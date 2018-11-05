-- Brute force translation of Variational relational algebra to SQL
module VDB.DBsetup.EnronEmailDB where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
--import qualified VDB.Condition as C
--import qualified VDB.Target as T
--import VDB.Variational
--import VDB.Value  

import Database.HDBC.Sqlite3

enronEmail :: IO Connection 
enronEmail = connectSqlite3 "test1.sqlite3"

--enronEmail :: Database
--enronEmail = Database (Ptr )

-- main = do liftIO $ print "don't go there"
--enronEmailEncode :: IO Database
--enronEmailEncode = undefined
{--enronEmailEncode = runSqlite ":memory:" $ do
    buildDb
    dumpTable


buildDb = do
    runMigration enronEmail
    insert $ PresCond "emp" "msg" "rec" "ref" 
    insert $ PresCond "emp" "msg" "rec" "ref" 
    insert $ PresCond "emp" "msg" "rec" "ref" 



dumpTable = rawQuery "select * from pres_cond" [] $$ CL.mapM_ (liftIO . print)

--}