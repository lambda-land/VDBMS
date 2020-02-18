-- | connecting to the employeed database.
module VDBMS.DBsetup.EmployeeDB where 

import Database.HDBC.Sqlite3

enronEmail :: IO Connection 
--enronEmail = connectSqlite3 "../../../databases/enronEmailDB/enronEmail.db"
enronEmail = connectSqlite3 "../../../databases/testDB/test1.db"


