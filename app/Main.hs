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
import VDB.Config

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
      -- qualifyQuery employeeVSchema $ variationizeQuery [empQ2_v1]
      vq = variationizeQuery [empQ1_v1]
      -- , empQ1_v2, empQ1_v3, empQ1_v4, empQ1_v5]
      qualifiedVq = qualifyQuery employeeVSchema vq
      vqManualEmpQ1_v1 = AChc (Ref $ Feature "v1") empQ1_v1 Empty
      vqManual = AChc (Ref $ Feature "v1") empQ1_v1 
                 (AChc (Or (Ref $ Feature "v2") (Ref $ Feature "v3")) empQ1_v2 
                  empQ1_v4and5)
  -- runTransFilterUnion vqManualEmpQ1_V1 p employeeVDB -- WORKS!!! HAVE NO IDEA IF IT'S CORRECT THO!!
  runTransFilterUnion vqManual p employeeVDB --WORKS!! TIME IT FOR SUBMISSION!!!
  -- Count time here ----------------------------
  -- putStrLn "Starting..."
  -- time $ runTransFilterUnion vqManual p employeeVDB  `seq` return ()
  -- putStrLn "Done."
  
      -- configs = [c1]
  -- runBrute q configs p "./databases/employeeDB/relDBs/" employeeVDB
  

c1 :: Config Bool
c1 (Feature "v1") = True 
c1 (Feature "v2") = False
c1 (Feature "v3") = False
c1 (Feature "v4") = False
c1 (Feature "v5") = False


-- main :: IO Connection
-- main = enronEmail
--main = return ()
