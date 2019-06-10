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

-- | Type of a relation in the database.
-- type RowType = [Opt (Attribute, Type)]
type RowType = Map Attribute (Opt SqlType)
type TableSchema = Opt RowType

-- | Attributes must be unique in a table. The pair (Int, Attribute)
--   is for keeping the order of attributes in a relation.
-- type UniqeAttribute = (Int, Attribute)


-- | Type of a relation in the database. 
--type RelationSchema = Map UniqeAttribute (Opt Type)


-- | A schema is a mapping from relations to row types. Both the map itself and
--   each row type are optionally included. The top-level 'Opt' corresponds to
--   the feature model, which defines the set of valid configurations.
type Schema = Opt (Map Relation (TableSchema))

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