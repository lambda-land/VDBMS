-- | Sqlite database.
module VDBMS.VDB.Database.Sqlite3.Sqlite where

import VDBMS.VDB.Schema.Variational.Schema
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

  disconnect (Sqlite3 _ _ c) = S.close c
  
  schema (Sqlite3 _ s _) = s 
  
  presCond (Sqlite3 p _ _) = p
  
  runQ = undefined


-- ex1 = Sqlite3 "../../../databases/testDB/test1.db" 