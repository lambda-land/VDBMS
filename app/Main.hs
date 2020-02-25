module Main where

import VDBMS.VDB.Database.HDBC.PostgreSQL
import VDBMS.VDB.Table.Table

-- Enron email VDB
import VDBMS.DBsetup.Postgres.EnronEmailDB
import VDBMS.UseCases.EnronUseCase.EnronQuery

-- Employee VDB
import VDBMS.DBsetup.Postgres.EmployeeDB
import VDBMS.UseCases.EmployeeUseCase.EmployeeQuery


-- approaches
import VDBMS.Approaches.ConfigQ.RunVariantQueryOnVDB (runQ1)
import VDBMS.Approaches.ConfigQ.RunVariantQueryOnVDBConcurrent (runQ4)
import VDBMS.Approaches.Linearize.RunOneQueryAtATime (runQ2)
import VDBMS.Approaches.Linearize.RunOneBigQuery (runQ3)
import VDBMS.Approaches.Linearize.RunQsConcurrent (runQ5)
-- runQ_i :: Database conn => conn -> Algebra -> IO Table

-- | Enron experiment.
main :: IO Table
main = 
  do enronvdb <- enronVDB
     -- runQ1 enronvdb q
     return undefined

-- -- | Employee experiment.
-- main :: IO Table
-- main = 
--   do empvdb <- employeeVDB
--      -- runQ1 empvdb q 
--      return undefined

-- main = return ()
