-- | HDBC library fetching result as Table.
module VDBMS.VDB.Database.HDBC.Fetch where

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database
import VDBMS.VDB.Table.Table

import Database.HDBC 


-- | fetchs result of a query in a table for any 
--   instance of IConnection.
fetch :: IConnection conn => conn -> Query -> IO Table
fetch c q = undefined
  -- do s <- prepare c q
  --    t <- fetchAllRowsMap s 
     

-- | stirct version of fetch.
fetch' :: IConnection conn => conn -> Query -> IO Table
fetch' = undefined