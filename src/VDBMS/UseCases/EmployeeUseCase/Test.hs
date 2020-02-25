-- | tests employee VDB.
module VDBMS.UseCases.EmployeeUseCase.Test where 


-- import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema
import VDBMS.DBsetup.Postgres.EmployeeDB (employeeVDB, empConn)

import VDBMS.VDB.Database.Tests

import Control.Monad.Catch 
import Control.Monad.IO.Class (liftIO, MonadIO)


import qualified Database.HDBC as H
import qualified Database.HDBC.PostgreSQL as P

-- isVschValid empVSchema
-- areConfsCorrect empVSchema [(empConfig1,empSchema1)]

-- | tests the consistency of schema and data of employee vdb.
testEmpVDB :: (MonadThrow m, MonadIO m) => m Bool
testEmpVDB = 
  do db <- liftIO employeeVDB
     isVDBvalid db

-- -- testingWhatsGoingWrong :: Bool
-- testingWhatsGoingWrong = 
--   do empconnection <- P.connectPostgreSQL empConn
--      -- H.getTables empconnection
--      -- H.quickQuery empconnection "SELECT * FROM v_dept;" []
--      s <- H.prepare empconnection "SELECT * FROM v_dept;"
--      -- _ <- H.execute s []
--      _ <- H.executeRaw s
--      H.fetchAllRowsMap s
--      -- putStrLn $ show res
--      -- H.commit empconnection
--      -- H.fetchAllRowsMap s