-- | connecting to the enron email database stored in the sqlite3 engine
--   via HDBC library
module VDBMS.DBsetup.Sqlite.EnronEmailDB where 

import VDBMS.VDB.Database.HDBC.Sqlite
import VDBMS.UseCases.EnronUseCase.EnronSchema (enronVSchema)
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Name

import Database.HDBC.Sqlite3

-- enronEmail :: IO Connection 
-- --enronEmail = connectSqlite3 "../../../databases/enronEmailDB/enronEmail.db"
-- enronEmail = connectSqlite3 "../../../databases/testDB/test1.db"

enronConn :: FilePath
enronConn = "../../../databases/enronEmailDB/enronEmail.db"

enronVDB :: IO SqliteHDBC
enronVDB = connect enronConn (Attribute "presCond") enronVSchema

