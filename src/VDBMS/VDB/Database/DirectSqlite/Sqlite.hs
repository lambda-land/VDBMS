-- | Sqlite database.
module VDBMS.VDB.Database.DirectSqlite.Sqlite where

-- import VDBMS.Features.Config
-- import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
-- import VDBMS.VDB.Table.Table
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.SQLite3 as S
import Data.Text

-- | A database residing in Sqlite and using directsqlite
--   to connect to it. 
data SqliteDirect = SqliteDirect PresCondAtt Schema S.Database

instance Database SqliteDirect where
  type Path SqliteDirect = Text
  connect t p s = do conn <- S.open t
                     return $ SqliteDirect p s conn
  disconnect (SqliteDirect p s c) = S.close c
  schema (SqliteDirect p s c) = s 
  presCond (SqliteDirect p s c) = p
  runQ = undefined

-- instance Database Text S.Database where 
--   data DB Text p s = Sqlite3 Text p s
--   data Connection Text S.Database = Sqlite3Conn Text S.Database
--   connection (Sqlite3 path p s) = S.open path
--   disconnect (Sqlite3Conn path d) = S.close d
--   schema (Sqlite3 path p s) = s 
--   presCond (Sqlite3 path p s) = p
--   runQ (Sqlite3 path p s) = undefined


-- ex1 = Sqlite3 "../../../databases/testDB/test1.db" 