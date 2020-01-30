-- | Sqlite database.
-- the database type class cannot be instantiated for the
-- database.sqlite3.sqlite because this library does not
-- provide any method to get the table returned by a query,
-- it only provides the exec and execPrint functions which
-- execute a query and the latter one prints result rows to
-- stdout.
module VDBMS.VDB.Database.Sqlite3.Sqlite where

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.SQLite3 as S
import Data.Text

-- | A database residing in Sqlite and using sqlite3
--   to connect to it. 
data Sqlite3 = Sqlite3 PCatt (Schema Bool) S.Database

instance Database Sqlite3 where

  type Path Sqlite3 = Text
  
  connect t p s = S.open t >>= return . Sqlite3 p s

  disconnect (Sqlite3 _ _ c) = S.close c
  
  schema (Sqlite3 _ s _) = s 
  
  presCond (Sqlite3 p _ _) = p
  
  fetchQRows = undefined

  fetchQRows' = undefined

  runQ = undefined


-- ex1 = Sqlite3 "../../../databases/testDB/test1.db" 