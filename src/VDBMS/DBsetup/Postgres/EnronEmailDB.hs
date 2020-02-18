-- | connecting to the enron email database stored in the sqlite3 engine
--   via HDBC library
module VDBMS.DBsetup.Postgres.EnronEmailDB where 

import Database.HDBC.Sqlite3

enronEmail :: IO Connection 
--enronEmail = connectSqlite3 "../../../databases/enronEmailDB/enronEmail.db"
enronEmail = connectSqlite3 "../../../databases/testDB/test1.db"


