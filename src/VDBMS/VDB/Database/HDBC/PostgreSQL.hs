-- | PostgreSQL database.
module VDBMS.VDB.Database.HDBC.PostgreSQL where

-- import VDBMS.Features.Config
-- import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
-- import VDBMS.VDB.Table.Table
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.HDBC as H
import qualified Database.HDBC.PostgreSQL as P

instance Database String P.Connection where 
  data DB String p s = PostgresHDBC String p s
  data Connection String P.Connection = PostgresConn String P.Connection
  connection (PostgresHDBC path p s) = P.connectPostgreSQL path
  disconnect (PostgresConn path c) = H.disconnect c
  schema (PostgresHDBC path p s) = s 
  presCond (PostgresHDBC path p s) = p
  runQ (PostgresHDBC path p s) = undefined


ex1 = PostgresHDBC "../../../databases/testDB/test1.db" 