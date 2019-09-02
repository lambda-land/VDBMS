-- | Database.
module VDBMS.VDB.Database.Database where

import VDBMS.Features.Config
import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Table.Table
import VDBMS.VDB.Name (PCatt)

-- | A query sent to the db engine is just a string.
type Query = String

-- | Database contains the path to the stored data,
--   the connection used to connect to it, the 
--   variational schema, and the presence condition 
--   attribute name. This is instantiated for each
--   external library and db engine used to connect to
--   and store the data.
class Database conn where 

  type Path conn 

  connect :: Path conn -> PCatt -> Schema -> IO conn 
  disconnect :: conn -> IO ()
  schema :: conn -> Schema
  presCond :: conn -> PCatt
  runQ :: conn -> Query -> IO Table
  -- | Gets all valid configuration of a vdb.
  getAllConfig :: conn -> [Config Bool]
  getAllConfig c = validConfsOfFexp $ featureModel $ schema c


