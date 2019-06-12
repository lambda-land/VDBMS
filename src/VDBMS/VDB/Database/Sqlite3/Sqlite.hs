-- | Sqlite database.
module VDBMS.VDB.Database.Sqlite3.Sqlite where

-- import VDBMS.Features.Config
-- import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
-- import VDBMS.VDB.Table.Table
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.SQLite3 as S
import Data.Text

-- | A database residing in Sqlite and using sqlite3
--   to connect to it. 
data Sqlite3 = Sqlite3 PresCondAtt Schema S.Database

instance Database Sqlite3 where

  type Path Sqlite3 = Text
  
  connect t p s = S.open t >>= return . Sqlite3 p s

  disconnect (Sqlite3 p s c) = S.close c
  
  schema (Sqlite3 p s c) = s 
  
  presCond (Sqlite3 p s c) = p
  
  runQ = undefined


-- ex1 = Sqlite3 "../../../databases/testDB/test1.db" 