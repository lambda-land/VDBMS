module Main where

import VDB.DBsetup.EnronEmailDB

import Database.HDBC.Sqlite3


main :: IO [[SqlValue]]
main = do
  employeeConn <- connectSqlite3 "/databases/employeeDB/emp_vdb.db"
  quickQuery' employeeConn "select * from v_job"

-- main :: IO Connection
-- main = enronEmail
--main = return ()
