-- | Sqlite database.
module VDBMS.VDB.Database.HDBC.Sqlite where

import VDBMS.VDB.Schema.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.HDBC as H
import qualified Database.HDBC.Sqlite3 as S

-- | Sqlite DBMS with HDBC interface.
data SqliteHDBC = SqliteHDBC PresCondAtt Schema S.Connection

instance Database SqliteHDBC where
  
  type Path SqliteHDBC = FilePath
  
  connect f p s = S.connectSqlite3 f >>= return . SqliteHDBC p s
  
  disconnect (SqliteHDBC p s c) = H.disconnect c
  
  schema (SqliteHDBC p s c) = s
  
  presCond (SqliteHDBC p s c) = p
  
  runQ = undefined



-- ex1 = SqliteHDBC "../../../databases/testDB/test1.db" 