-- | tests employee VDB.
module VDBMS.UseCases.EnronUseCase.Test where 


-- import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema
import VDBMS.DBsetup.Postgres.EnronEmailDB (enronVDB)

import VDBMS.VDB.Database.Tests

import Control.Monad.Catch 
import Control.Monad.IO.Class (liftIO, MonadIO)


-- isVschValid empVSchema
-- areConfsCorrect empVSchema [(empConfig1,empSchema1)]

-- | tests the consistency of schema and data of enron vdb.
testEnronVDB :: (MonadThrow m, MonadIO m) => m Bool
testEnronVDB = 
  do db <- liftIO enronVDB
     isVDBvalid db