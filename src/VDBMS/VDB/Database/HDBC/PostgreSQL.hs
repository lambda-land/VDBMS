-- | PostgreSQL database.
module VDBMS.VDB.Database.HDBC.PostgreSQL where

import VDBMS.VDB.Schema.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database

import qualified Database.HDBC as H
import qualified Database.HDBC.PostgreSQL as P

-- | Postgresql DBMS with HDBC interface.
data PostgresHDBC = PostgresHDBC PresCondAtt Schema P.Connection

instance Database PostgresHDBC where
  
  type Path PostgresHDBC = String 

  connect f p s = P.connectPostgreSQL f >>= return . PostgresHDBC p s

  disconnect (PostgresHDBC p s c) = H.disconnect c
  
  schema (PostgresHDBC p s c) = s
  
  presCond (PostgresHDBC p s c) = p 
  
  runQ (PostgresHDBC p s c) = undefined


-- ex1 = PostgresHDBC "../../../databases/testDB/test1.db" 