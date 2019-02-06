module Main where

import VDB.DBsetup.EnronEmailDB

import VDB.Example.EmployeeUseCase.EmployeeVSchema
import VDB.Example.EmployeeUseCase.EmployeeSchema
import VDB.Example.EmployeeUseCase.EmployeeQuery
import VDB.Example.EmployeeUseCase.EmployeeVQuery
import VDB.Database
import VDB.VTable
import VDB.Name
import VDB.Approach1.App1Run
import VDB.BruteForceApproach.BruteForce
import VDB.Algebra
import VDB.Name
import VDB.FeatureExpr
import VDB.Config
import VDB.SqlTable
import VDB.Variant

import Database.HDBC
import Database.HDBC.Sqlite3

import System.Directory
import System.Clock
import System.CPUTime
import Text.Printf

-- import VDB.Example.EmployeeUseCase.SmallSampleForTest


time :: IO t -> IO t
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "Computation time: %0.5f sec\n" (diff :: Double)
    return v
 
-- vqManual = AChc (Ref $ Feature "v1") empQ1_v1 
--                  (AChc (Or (Ref $ Feature "v2") (Ref $ Feature "v3")) empQ1_v2 
--                   empQ1_v4and5)

employeeConn = connectSqlite3 "./databases/employeeDB/emp_vdb.db"
p = PresCondAtt "presCond"
employeeVSchema = variationizeSchema [empSchema1, empSchema2, empSchema3, empSchema4, empSchema5]
employeeVDB = do
  conn <- employeeConn
  return $ VDB employeeVSchema conn


-- main :: IO VTable
-- main :: IO [[SqlValue]]
main = do 
  -- path <- getCurrentDirectory
  -- testdb <- connectSqlite3 "/databases/testDB/test1.db"
  -- /Volumes/GoogleDrive/My Drive/OSU/Research/VDBMSgit/codes/VDBMS/databases/employeeDB/emp_vdb.db
  -- employeeConn <- connectSqlite3 "./databases/employeeDB/emp_vdb.db"
  -- conn <- employeeConn
  vdb <- employeeVDB
  -- let p = PresCondAtt "presCond"
  --     employeeVSchema = variationizeSchema [empSchema1, empSchema2, empSchema3, empSchema4, empSchema5]
  --     employeeVDB = VDB employeeVSchema employeeConn
      -- vqManual = AChc (Ref $ Feature "v1") empQ1_v1 
      --            (AChc (Or (Ref $ Feature "v2") (Ref $ Feature "v3")) empQ1_v2 
      --             empQ1_v4and5)
  -- configVDB "./databases/employeeDB/confed/emp_confed" p vdb c1 1
  configVDB "./databases/employeeDB/confed/emp_confed" p vdb c2 2 -- EXCEPTION:
  -- configVDB "./databases/employeeDB/confed/emp_confed" p employeeVDB c3 3
  -- configVDB "./databases/employeeDB/confed/emp_confed" p employeeVDB c4 4
  -- configVDB "./databases/employeeDB/confed/emp_confed" p vdb c5 5
  --     q = empQ2_v1
      -- qualifyQuery employeeVSchema $ variationizeQuery [empQ2_v1]
      -- vq = variationizeQuery [empQ1_v1]
      -- , empQ1_v2, empQ1_v3, empQ1_v4, empQ1_v5]
      -- qualifiedVq = qualifyQuery employeeVSchema vq
      -- vqManualEmpQ1_v1 = AChc (Ref $ Feature "v1") empQ1_v1 Empty
      -- dbs = [db1,db2,db3,db4,db5]
  -- runTransFilterUnion vqManualEmpQ1_V1 p employeeVDB -- WORKS!!! HAVE NO IDEA IF IT'S CORRECT THO!!
  -- runTransFilterUnion vqManual p employeeVDB --WORKS!! TIME IT FOR SUBMISSION!!!
  -- runTransFilterUnion vq p employeeVDB
  -- Count time here ----------------------------
  -- putStrLn "Starting..."
  -- time $ runTransFilterUnion vqManual p employeeVDB -- 4.08534 sec, 4.25021 sec
  -- putStrLn "Done."
  --     configs = [c1,c2,c3,c4,c5]
  --     q1 = "select empno, name, hiredate from v_engineerpersonnel union select empno, name, hiredate from v_otherpersonnel;"
  --     q2 = "select empno, name, hiredate from v_empacct;"
  --     q3 = "select empno, name, hiredate from v_empacct;"
  --     q4 = "select v_empacct.empno, name, hiredate from v_empacct inner join v_empbio;"
  --     q5 = "select v_empacct.empno, firstname, lastname, hiredate from v_empacct inner join v_empbio;"
  --     -- qs = [q1,q2,q3,q4,q5]
  --     -- vqs = zip qs configs
  -- putStrLn "Starting..."    
  -- conn1 <- connectSqlite3 "./databases/employeeDB/relDBs/emp1.db"
  -- let db1 = VariantDB empSchema1 (conn1,c1)
  -- time $ runq c1 q1 db1
  -- disconnect conn1
  -- conn2 <- connectSqlite3 "./databases/employeeDB/relDBs/emp2.db"
  -- let db2 = VariantDB empSchema2 (conn2,c2)
  -- time $ runq c2 q2 db2
  -- disconnect conn2
  -- conn3 <- connectSqlite3 "./databases/employeeDB/relDBs/emp3.db"
  -- let db3 = VariantDB empSchema3 (conn3,c3)
  -- time $ runq c3 q3 db3
  -- disconnect conn3
  -- conn4 <- connectSqlite3 "./databases/employeeDB/relDBs/emp4.db"
  -- let db4 = VariantDB empSchema4 (conn4,c4)
  -- time $ runq c4 q4 db4
  -- disconnect conn4
  -- conn5 <- connectSqlite3 "./databases/employeeDB/relDBs/emp5.db"
  -- let db5 = VariantDB empSchema5 (conn5,c5)
  -- time $ runq c5 q5 db5
  -- disconnect conn5
  -- putStrLn "Done."
-- Starting...
-- Computation time: 0.01079 sec
-- Computation time: 0.01708 sec
-- Computation time: 0.01880 sec
-- Computation time: 48.24207 sec
-- Computation time: 50.10460 sec
-- Done


  -- putStrLn "Starting..."    
  -- time $ runSqlQsOnCorrespDBs vqs dbs --23.47896 sec
  -- putStrLn "Done."

  -- putStrLn "Starting..."    
  -- time $ bruteForSigmod vqManual configs dbs -- 105.11169 sec, 108.28369 sec, 100.95015 sec, 23.47896 sec
  -- putStrLn "Done."
  -- runBrute' q configs p "./databases/employeeDB/relDBs/emp_db" employeeVDB
  

-- bruteForSigmod :: Algebra -> [Config Bool] 
--             -> [SqlDatabase Connection] -> IO [SqlVariantTable]
 -- VariantDB :: IConnection conn => Schema -> Variant conn Bool -> SqlDatabase conn 
-- db1 :: SqlDatabase Connection
-- db1 = VariantDB empSchema1 (conn1,c1) 



-- Commented code was HARD CODED FOR THE SIGMOD 19 DEMO SUBMISSION!!
-- runq :: IConnection conn => Config Bool -> String -> SqlDatabase conn -> IO SqlVariantTable
-- runq c t db = do 
--   q <- mkStatement db t 
--   _ <- execute q []
--   r <- fetchAllRowsMap' q
--   return $ mkVariant r c



c1 :: Config Bool
c1 (Feature "v1") = True 
c1 (Feature "v2") = False
c1 (Feature "v3") = False
c1 (Feature "v4") = False
c1 (Feature "v5") = False


c2 :: Config Bool
c2 (Feature "v1") = False 
c2 (Feature "v2") = True
c2 (Feature "v3") = False
c2 (Feature "v4") = False
c2 (Feature "v5") = False

c3 :: Config Bool
c3 (Feature "v1") = False 
c3 (Feature "v2") = False
c3 (Feature "v3") = True
c3 (Feature "v4") = False
c3 (Feature "v5") = False

c4 :: Config Bool
c4 (Feature "v1") = False 
c4 (Feature "v2") = False
c4 (Feature "v3") = False
c4 (Feature "v4") = True
c4 (Feature "v5") = False

c5 :: Config Bool
c5 (Feature "v1") = False 
c5 (Feature "v2") = False
c5 (Feature "v3") = False
c5 (Feature "v4") = False
c5 (Feature "v5") = True


-- main :: IO Connection
-- main = enronEmail
--main = return ()
