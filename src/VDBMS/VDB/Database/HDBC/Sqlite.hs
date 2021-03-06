-- | Sqlite database.
module VDBMS.VDB.Database.HDBC.Sqlite where

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Database.HDBC.Fetch

import qualified Database.HDBC as H
import qualified Database.HDBC.Sqlite3 as S

-- | Sqlite DBMS with HDBC interface.
data SqliteHDBC = SqliteHDBC PCatt Schema S.Connection

instance Database SqliteHDBC where
  
  type Path SqliteHDBC = FilePath
  
  connect f p s = S.connectSqlite3 f >>= return . SqliteHDBC p s
  
  disconnect (SqliteHDBC _ _ c) = H.disconnect c
  
  schema (SqliteHDBC _ s _) = s
  
  presCond (SqliteHDBC p _ _) = p
  
  fetchQRows (SqliteHDBC _ _ c) = fetch c

  fetchQRows' (SqliteHDBC _ _ c) = fetch' c

  runQ (SqliteHDBC _ _ _) = undefined



-- ex1 = SqliteHDBC "../../../databases/testDB/test1.db" 