-- | PostgreSQL database.
module VDBMS.VDB.Database.HDBC.PostgreSQL where

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Database.HDBC.Fetch 

import qualified Database.HDBC as H
import qualified Database.HDBC.PostgreSQL as P

-- | Postgresql DBMS with HDBC interface.
data PostgresHDBC = PostgresHDBC PCatt Schema P.Connection

instance Database PostgresHDBC where
  
  type Path PostgresHDBC = String 

  connect f p s = P.connectPostgreSQL f >>= return . PostgresHDBC p s

  disconnect (PostgresHDBC _ _ c) = H.disconnect c
  
  schema (PostgresHDBC _ s _) = s
  
  presCond (PostgresHDBC p _ _) = p 
  
  fetchQRows (PostgresHDBC _ _ c) = fetch c 

  fetchQRows' (PostgresHDBC _ _ c) = fetch' c

  runQ (PostgresHDBC _ _ _) = undefined


-- ex1 = PostgresHDBC "../../../databases/testDB/test1.db" 