-- | connecting to the enron email database stored in postgres.
module VDBMS.DBsetup.Postgres.EnronEmailDB where 

import VDBMS.VDB.Database.HDBC.PostgreSQL
import VDBMS.UseCases.EnronUseCase.EnronSchema (enronVSchema)
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Name

import Database.HDBC.PostgreSQL

-- | enron connection.
-- for other options look into:
-- https://www.postgresql.org/docs/8.1/libpq.html#LIBPQ-CONNECT
enronConn :: String 
-- enronConn = "host=localhost dbname=enron user=postgres password=paris1993"
enronConn = "dbname=enron user=ataeip"

-- | enron VDB
enronVDB :: IO PostgresHDBC
enronVDB = connect enronConn (Attribute "prescond") enronVSchema

