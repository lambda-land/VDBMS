-- | Variational database schema types.
module VDBMS.VDB.Schema.Relational.Types (

        RTableSchema(..),
        RSchema(..),
        RSchemaError(..)

) where

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Data.Map.Strict (Map)

import Control.Monad.Catch (Exception)

import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value

-- | Type of a relation in a relational database.
type RTableSchema = Map Attribute SqlType

-- | A relational schema is a mapping from relations to table schemas.
type RSchema = Map Relation (RTableSchema)

-- | Errors querying schema.
data RSchemaError = RMissingRelation Relation
                  | RMissingAttribute Attribute
  deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception RSchemaError