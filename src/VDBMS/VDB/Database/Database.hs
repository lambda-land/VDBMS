-- | Database.
module VDBMS.VDB.Database.Database where

import VDBMS.Features.Config
import VDBMS.Features.Feature (Feature)
import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Table.Table (Table)
import VDBMS.DBMS.Table.Table (SqlTable)
import VDBMS.VDB.Name (PCatt)
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)

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

  connect :: Path conn -> PCatt -> Schema Bool -> IO conn 
  disconnect :: conn -> IO ()
  schema :: conn -> Schema Bool
  presCond :: conn -> PCatt
  fetchQRows :: conn -> Query -> IO SqlTable
  fetchQRows' :: conn -> Query -> IO SqlTable -- strict version
  -- when you know which approach to use fill this in for instances.
  runQ :: conn -> Algebra -> IO Table
  -- | gets all features of VDB.
  dbFeatures :: conn -> [Feature]
  dbFeatures = schFeatures . schema
  -- | Gets all valid configuration of a vdb.
  getAllConfig :: conn -> [Config Bool]
  getAllConfig c = schConfs $ schema c


