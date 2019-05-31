-- | Sqlite database.
module VDBMS.VDB.Database.HDBC.Sqlite where

-- import VDBMS.Features.Config
-- import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
-- import VDBMS.VDB.Table.Table
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.HDBC as H
import qualified Database.HDBC.Sqlite3 as S

instance Database FilePath S.Connection where 
  data DB FilePath p s = SqliteHDBC FilePath p s
  data Connection FilePath S.Connection = SqliteConn FilePath S.Connection
  connection (SqliteHDBC path p s) = S.connectSqlite3 path
  disconnect (SqliteConn p c) = H.disconnect c
  schema (SqliteHDBC path p s) = s 
  presCond (SqliteHDBC path p s) = p
  runQ (SqliteHDBC path p s) = undefined


ex1 = SqliteHDBC "../../../databases/testDB/test1.db" 