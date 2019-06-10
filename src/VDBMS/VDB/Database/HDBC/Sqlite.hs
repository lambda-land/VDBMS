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

-- discuss with Eric
-- data HDBCdb conn = HDBCdb PresCondAtt Schema conn 

-- instance H.IConnection conn => H.IConnection (HDBCdb conn) where
--   disconnect (HDBCdb p s c) = H.disconnect c
--   commit (HDBCdb p s c) = H.commit c
--   rollback (HDBCdb p s c) = H.rollback c
--   run (HDBCdb p s c) = H.run c
--   prepare (HDBCdb p s c) = H.prepare c
--   clone (HDBCdb p s c) = do conn <- H.clone c 
--                             return $ HDBCdb p s conn
--   hdbcDriverName (HDBCdb p s c) = H.hdbcDriverName c
--   hdbcClientVer (HDBCdb p s c) = H.hdbcClientVer c
--   proxiedClientName (HDBCdb p s c) = H.proxiedClientName c
--   proxiedClientVer (HDBCdb p s c) = H.proxiedClientVer c
--   dbServerVer (HDBCdb p s c) = H.dbServerVer c
--   dbTransactionSupport (HDBCdb p s c) = H.dbTransactionSupport c
--   getTables (HDBCdb p s c) = H.getTables c
--   describeTable (HDBCdb p s c) = H.describeTable c

-- instance H.IConnection conn => Database (HDBCdb conn) where
--   type Path (HDBCdb conn) = FilePath
--   connect = undefined
--   -- disconnect conn = H.disconnect conn 
--   disconnect (HDBCdb p s c) = H.disconnect c
--   schema (HDBCdb p s c) = s
--   runQ = undefined

data SqliteHDBC = SqliteHDBC PresCondAtt Schema S.Connection

instance Database SqliteHDBC where
  type Path SqliteHDBC = FilePath
  connect f p s = do conn <- S.connectSqlite3 f
                     return $ SqliteHDBC p s conn 
  disconnect (SqliteHDBC p s c) = H.disconnect c
  schema (SqliteHDBC p s c) = s
  presCond (SqliteHDBC p s c) = p
  runQ = undefined



-- ex1 = SqliteHDBC "../../../databases/testDB/test1.db" 