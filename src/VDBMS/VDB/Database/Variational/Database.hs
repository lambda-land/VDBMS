-- | Variational database.
module VDBMS.VDB.Database.Variational.Database where

import VDBMS.VDB.Schema.Schema
import VDBMS.Features.Config
import VDBMS.VDB.Name
import VDBMS.Features.ConfFexp

-- | a variational database. c is the connection to the DB.
data VDB c = VDB {
    schema     :: Schema
  , presCond   :: PresCondAtt
  , connection :: c
} 


-- | generates the valid configurations of a variational database.
getAllConfig :: VDB c -> [Config Bool]
getAllConfig db = validConfsOfFexp $ featureModel $ schema db
