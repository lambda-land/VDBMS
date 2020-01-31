-- | MySql database.
module VDBMS.VDB.Database.HDBC.MySql where

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Database.HDBC.Fetch

-- import qualified Database.HDBC as H
-- import qualified Database.HDBC.MySql as M

-- -- | MySql DBMS with HDBC interface.
-- data MySqlHDBC = MySql PCatt Schema M.Connection

-- instance Database MySqlHDBC where
  
--   type Path MySqlHDBC = M.MySQLConnectInfo 
  
--   connect f p s = M.connectMySQL f >>= return . MySqlHDBC p s
  
--   disconnect (MySqlHDBC _ _ c) = H.disconnect c
  
--   schema (MySqlHDBC _ s _) = s
  
--   presCond (MySqlHDBC p _ _) = p
  
--   fetchQRows (MySqlHDBC _ _ c) = fetch c

--   fetchQRows' (MySqlHDBC _ _ c) = fetch' c

--   runQ (MySqlHDBC _ _ _) = undefined


-- -- data MySQLConnectInfo = MySQLConnectInfo
-- --     { -- | The server's hostname; e.g., @\"db1.example.com\"@
-- --       mysqlHost       :: String
-- --       -- | The MySQL username to use for login; e.g., @\"scott\"@
-- --     , mysqlUser       :: String
-- --       -- | The MySQL password to use for login; e.g., @\"tiger\"@
-- --     , mysqlPassword   :: String
-- --       -- | the \"default\" database name; e.g., @\"emp\"@
-- --     , mysqlDatabase   :: String
-- --       -- | The port on which to connect to the server; e.g., @3306@
-- --     , mysqlPort       :: Int
-- --       -- | The absolute path of the server's Unix socket; e.g., @\"\/var\/lib\/mysql.sock\"@
-- --     , mysqlUnixSocket :: String
-- --       -- | The group name in my.cnf from which it reads options; e.g., @\"test\"@
-- --     , mysqlGroup      :: Maybe String
-- --     }

-- -- ex1 = SqliteHDBC "../../../databases/testDB/test1.db" 