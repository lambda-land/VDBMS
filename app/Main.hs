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
import VDB.Algebra
import VDB.Name
import VDB.FeatureExpr

import Database.HDBC
import Database.HDBC.Sqlite3

import System.Directory
import System.Clock
import System.CPUTime
import Text.Printf

import VDB.Example.EmployeeUseCase.SmallSampleForTest


time :: IO t -> IO t
time a = do
    start <- getCPUTime
    v <- a
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "Computation time: %0.5f sec\n" (diff :: Double)
    return v
 

-- main :: IO VTable
-- main :: IO [[SqlValue]]
main = do 
  path <- getCurrentDirectory
  -- testdb <- connectSqlite3 "/databases/testDB/test1.db"
  -- /Volumes/GoogleDrive/My Drive/OSU/Research/VDBMSgit/codes/VDBMS/databases/employeeDB/emp_vdb.db
  employeeConn <- connectSqlite3 "./databases/employeeDB/emp_vdb.db"
  let employeeVSchema = variationizeSchema [empSchema1, empSchema2, empSchema3, empSchema4, empSchema5]
      employeeVDB = VDB employeeVSchema employeeConn
      p = PresCondAtt "presCond"
      q = empQ2_v1
{-
VTable (FAlSE OR ((((((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND NOT v4) OR (NOT ((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND v4)) AND NOT v5) OR (NOT ((((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND NOT v4) OR (NOT ((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND v4)) AND v5)),
fromList [(Attribute {attributeQualifier = Nothing, attributeName = "title"},((((((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND NOT v4) OR (NOT ((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND v4)) AND NOT v5) OR (NOT ((((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND NOT v4) OR (NOT ((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR (NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND v4)) AND v5),TByteString))]) 
[fromList [("title",SqlByteString "Senior Engineer")],
fromList [("title",SqlByteString "Staff")],
fromList [("title",SqlByteString "Engineer")],
fromList [("title",SqlByteString "Senior Staff")],
fromList [("title",SqlByteString "Assistant Engineer")],
fromList [("title",SqlByteString "Technique Leader")]]
-}      
      -- qualifyQuery employeeVSchema $ variationizeQuery [empQ2_v1]
      vq = variationizeQuery [empQ1_v1, empQ1_v2, empQ1_v3, empQ1_v4, empQ1_v5]
 
      qualifiedVq = qualifyQuery employeeVSchema vq
      vqManual = AChc (Ref $ Feature "v1") empQ1_v1 Empty

  -- runTransFilterUnion vqManual p employeeVDB -- WORKS!!! HAVE NO IDEA IF IT'S CORRECT THO!!
  runTransFilterUnion vq p employeeVDB
  -- Count time here ----------------------------
  -- putStrLn "Starting..."
  -- time $ runTransFilterUnion vqManual p employeeVDB  `seq` return ()
  -- putStrLn "Done."
  
  -- runTransFilterUnion q p employeeVDB
  -- quickQuery' employeeConn "select * from v_job" []
  -- run testdb "CREATE TABLE test (id INTEGER NOT NULL, desc VARCHAR(80))" []


-- runTransFilterUnion :: IConnection conn => Algebra -> PresCondAtt 
--                        -> SqlDatabase conn -> IO (VTable)


-- main :: IO Connection
-- main = enronEmail
--main = return ()
