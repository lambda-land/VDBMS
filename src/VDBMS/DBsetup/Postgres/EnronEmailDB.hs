-- | connecting to the enron email database stored in postgres.
module VDBMS.DBsetup.Postgres.EnronEmailDB where 

import VDBMS.VDB.Database.HDBC.PostgreSQL
import VDBMS.UseCases.EnronUseCase.EnronSchema (enronVSchema)
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Name

import Database.HDBC.PostgreSQL

-- | enron connection.
enronConn :: String 
enronConn = "blah"

-- | enron VDB
enronVDB :: IO PostgresHDBC
enronVDB = connect enronConn (Attribute "presCond") enronVSchema

