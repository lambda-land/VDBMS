-- | connecting to the employeed database stored in postgres.
module VDBMS.DBsetup.Postgres.EmployeeDB where 

import VDBMS.VDB.Database.HDBC.PostgreSQL
import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema (empVSchema)
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Name

import Database.HDBC.PostgreSQL

-- | employee connection.
-- for other options look into:
-- https://www.postgresql.org/docs/8.1/libpq.html#LIBPQ-CONNECT
empConn :: String 
empConn = "host=localhost dbname=employees user=postgres password=paris1993"
-- empConn = "host=localhost dbname=employees user=postgres password=paris1993"

-- | employee VDB
employeeVDB :: IO PostgresHDBC
employeeVDB = connect empConn (Attribute "prescond") empVSchema
