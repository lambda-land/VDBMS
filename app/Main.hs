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

import Database.HDBC
import Database.HDBC.Sqlite3

import System.Directory

-- main :: IO VTable
-- main :: IO [[SqlValue]]
main = do 
  path <- getCurrentDirectory
  testdb <- connectSqlite3 "/databases/testDB/test1.db"
  -- /Volumes/GoogleDrive/My Drive/OSU/Research/VDBMSgit/codes/VDBMS/databases/employeeDB/emp_vdb.db
  employeeConn <- connectSqlite3 "databases/employeeDB/emp_vdb.db"
  let employeeVSchema = variationizeSchema [empSchema1, empSchema2, empSchema3, empSchema4, empSchema5]
      employeeVDB = VDB employeeVSchema employeeConn
      p = PresCondAtt "presCond"
      q = empQ2_v1
      -- qualifyQuery employeeVSchema $ variationizeQuery [empQ2_v1]
      -- vq = variationizeQuery [empQ1_v1, empQ1_v2, empQ1_v3, empQ1_v4, empQ1_v5]
      -- qualifiedVq = qualifyQuery employeeVSchema vq
  -- runTransFilterUnion qualifiedVq p employeeVDB
  -- runTransFilterUnion q p employeeVDB
  quickQuery' employeeConn "select * from v_job" []
  -- run testdb "CREATE TABLE test (id INTEGER NOT NULL, desc VARCHAR(80))" []


-- runTransFilterUnion :: IConnection conn => Algebra -> PresCondAtt 
--                        -> SqlDatabase conn -> IO (VTable)

-- main :: IO Connection
-- main = enronEmail
--main = return ()
