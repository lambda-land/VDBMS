-- | Database.
module VDBMS.VDB.Database.Database where

import VDBMS.Features.Config
import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
import VDBMS.VDB.Table.Table

type Query = String

class Database path c | path -> c where
  data DB path :: * -> * -> *
  data Connection path c :: *
  connection :: DB path p s -> IO c
  disconnect :: Connection path c -> IO ()
  schema :: DB path p s -> s
  presCond :: DB path p s -> p
  -- mkStmt :: DB c p s -> String -> IO Stmt
  runQ :: DB path p s -> Query -> IO Table



getAllConfig :: Database path c => DB path p Schema -> [Config Bool]
getAllConfig db = validConfsOfFexp $ featureModel $ schema db

  


