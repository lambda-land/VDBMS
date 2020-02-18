-- | connecting to the employeed database stored in postgres.
module VDBMS.DBsetup.Postgres.EmployeeDB where 

import VDBMS.VDB.Database.HDBC.PostgreSQL
import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema (empVSchema)
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Name

import Database.HDBC.PostgreSQL

-- | employee connection.
empConn :: String 
empConn = "blah"

-- | employee VDB
employeeVDB :: IO PostgresHDBC
employeeVDB = connect empConn (Attribute "presCond") empVSchema
