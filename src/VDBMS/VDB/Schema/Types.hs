-- | Variational database schema types.
module VDBMS.VDB.Schema.Types (

        RowType(..),
        TableSchema(..),
        Schema(..),
        SchemaError(..),
        featureModel,
        schemaStrct

) where

import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Data.Map.Strict (Map)

import Control.Monad.Catch (Exception)

import VDBMS.VDB.Name
import VDBMS.Variational.Opt
import VDBMS.DBMS.Value.Value
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Schema.Relational.Types
import VDBMS.Variational.Variational
import VDBMS.Features.Config (Config)

-- | Type of a relation in the database.
type RowType = Map Attribute (Opt SqlType)

-- | Schema of a table in a variational database.
type TableSchema = Opt RowType

-- | A schema is a mapping from relations to row types. Both the map itself and
--   each row type are optionally included. The top-level 'Opt' corresponds to
--   the feature model, which defines the set of valid configurations.
type Schema = Opt (Map Relation (TableSchema))

-- | Configures a variational schema to a relational one.
configSchema :: Config Bool -> Schema -> RSchema
configSchema = undefined

-- | Linearizes a variational schema.
linearizeSchema :: Schema -> [Opt RSchema]
linearizeSchema = undefined

instance Variational Schema where
  type NonVariational Schema = RSchema 

  type Variant Schema = Opt RSchema

  configure = configSchema

  linearize = linearizeSchema

-- | Type of a relation in a relational database.
-- type RTableSchema = Map Attribute SqlType

-- -- | A relational schema is a mapping from relations to table schemas.
-- type RSchema = Map Relation (RTableSchema)


-- | The feature model associated with a schema.
featureModel :: Schema -> FeatureExpr
featureModel = getFexp

-- | Gets the structure of schema.
schemaStrct :: Schema -> Map Relation TableSchema
schemaStrct = getObj 

-- | Errors querying schema.
data SchemaError = MissingRelation Relation
                 | MissingAttribute Attribute
  deriving (Data,Eq,Generic,Ord,Read,Show,Typeable)

instance Exception SchemaError

