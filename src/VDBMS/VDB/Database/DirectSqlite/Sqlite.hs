-- | A slightly lower-level version of Sqlite3 database.
module VDBMS.VDB.Database.DirectSqlite.Sqlite where

-- import VDBMS.Features.Config
-- import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Variational.Schema
-- import VDBMS.VDB.Table.Table
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.SQLite3.Direct as S
import Data.Text

-- | A database residing in Sqlite and using directsqlite
--   to connect to it. 
data SqliteDirect = SqliteDirect PresCondAtt Schema S.Database

-- instance Database SqliteDirect where
--   type Path SqliteDirect = Text
--   connect t p s = do conn <- S.open t
--                      return $ SqliteDirect p s conn
--   disconnect (SqliteDirect p s c) = S.close c
--   schema (SqliteDirect p s c) = s 
--   presCond (SqliteDirect p s c) = p
--   runQ = undefined

