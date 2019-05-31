-- | Variant database.
module VDBMS.VDB.Database.Variant.Database where

import VDBMS.VDB.Schema.Schema
import VDBMS.Features.Config
import VDBMS.VDB.Name

-- | a variant database. c is the connection to the underlying db.
data VariantDB b c = VariantDB {
    schema     :: Schema
  , config     :: Config b
  , connection :: c 
}

