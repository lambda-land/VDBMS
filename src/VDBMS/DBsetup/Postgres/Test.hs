-- | connecting to the employeed database stored in postgres.
module VDBMS.DBsetup.Postgres.Test where 

import VDBMS.VDB.Database.HDBC.PostgreSQL
import VDBMS.UseCases.Test.Schema 
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Name

import Database.HDBC.PostgreSQL

-- | test connection.
-- for other options look into:
-- https://www.postgresql.org/docs/8.1/libpq.html#LIBPQ-CONNECT
tstConn :: String 
tstConn = "host=localhost dbname=test user=postgres password=paris1993"
-- tstConn = "dbname=test user=ataeip"

-- | test VDB with schema sone
tstVDBone :: IO PostgresHDBC
tstVDBone = connect tstConn (Attribute "prescond") sone

-- | test VDB with schema sonefeone
tstVDBonefeone :: IO PostgresHDBC
tstVDBonefeone = connect tstConn (Attribute "prescond") sonefeone

-- | test VDB with schema stwo
tstVDBtwo :: IO PostgresHDBC
tstVDBtwo = connect tstConn (Attribute "prescond") stwo

-- | test VDB with schema sthree
tstVDBthree :: IO PostgresHDBC
tstVDBthree = connect tstConn (Attribute "prescond") sthree

-- | test VDB with schema sone'
tstVDBone' :: IO PostgresHDBC
tstVDBone' = connect tstConn (Attribute "prescond") sone'

-- | test VDB with schema stwo'
tstVDBtwo' :: IO PostgresHDBC
tstVDBtwo' = connect tstConn (Attribute "prescond") stwo'

-- | test VDB with schema sthree'
tstVDBthree' :: IO PostgresHDBC
tstVDBthree' = connect tstConn (Attribute "prescond") sthree'

