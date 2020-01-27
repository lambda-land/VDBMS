-- | HDBC library fetching result as Table.
module VDBMS.VDB.Database.HDBC.Fetch where

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.Database.Database
-- import VDBMS.VDB.Table.Table
import VDBMS.DBMS.Table.Table (SqlTable)
import Database.HDBC 


-- data Table = Table TableSchema SqlTable
-- type TableSchema = Opt RowType
-- type RowType = Map Attribute (Opt SqlType)
-- type Opt a = (FeatureExpr, a)
-- type SqlTable = [SqlRow]
-- type SqlRow = Map String SqlValue


-- | fetchs result of a query in a table for any 
--   instance of IConnection.
fetch :: IConnection conn => conn -> Query -> IO SqlTable
fetch c q = 
  do s <- prepare c q
     fetchAllRowsMap s 
     

-- | stirct version of fetch.
fetch' :: IConnection conn => conn -> Query -> IO SqlTable
fetch' c q = 
  do s <- prepare c q
     fetchAllRowsMap' s

