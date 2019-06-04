-- | Database.
module VDBMS.VDB.Database.Database where

import VDBMS.Features.Config
import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
import VDBMS.VDB.Table.Table

-- | A query sent to the db engine is just a string.
type Query = String

-- | Database contains the path to the stored data,
--   the connection used to connect to it, the 
--   variational schema, and the presence condition 
--   attribute name. This is instantiated for each
--   external library and db engine used to connect to
--   and store the data.
class Database path c | path -> c where
  data DB path :: * -> * -> *
  data Connection path c :: *
  connection :: DB path p s -> IO c
  disconnect :: Connection path c -> IO ()
  schema :: DB path p s -> s
  presCond :: DB path p s -> p
  -- mkStmt :: DB c p s -> String -> IO Stmt
  runQ :: DB path p s -> Query -> IO Table


-- | Gets all valid configuration of a vdb.
getAllConfig :: Database path c => DB path p Schema -> [Config Bool]
getAllConfig db = validConfsOfFexp $ featureModel $ schema db

  


