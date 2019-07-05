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

import Data.Map.Strict (Map, mapMaybe)

import Control.Monad.Catch 

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
configSchema :: MonadThrow m => Config Bool -> Schema -> m RSchema
configSchema c s 
  | evalFeatureExpr c fm = 
    return $ mapMaybe (configTableSchema c) (schemaStrct s)
  | otherwise = throwM $ InvalidConfig fm
    where
      fm = featureModel s

-- | Configures a variational table schema to the relational one.
configTableSchema :: MonadThrow m => Config Bool -> TableSchema -> m RTableSchema
configTableSchema c t 
  | evalFeatureExpr c tablePresCond 
    = return $ mapMaybe (configAttribute c) table
  | otherwise = throwM $ InvalidConfig tablePresCond
    where 
      tablePresCond = getFexp t
      table = getObj t
      configAttribute c ot 
        | evalFeatureExpr c (getFexp ot) = Just $ getObj ot
        | otherwise = Nothing


-- | Linearizes a variational schema.
--   Conjuncts schema's feature expression with the generated opt
--   of linearizing table schema, if satisfiable it includes the relation
--   in the relational schema if not it doesn't include it. Also, the new
--   fexp is the conjuncted one.
linearizeSchema :: Schema -> [Opt RSchema]
linearizeSchema = undefined

-- | Linearizes a rowtype.
--   Helper for linearizeTableSch.
linearizeAttrs :: RowType -> [Opt RTableSchema]
linearizeAttrs = undefined

-- | Conjuncts the fexp of variational table schema 
--   with the feature expression assigned to a relational table schema
--   and if its satisfiable it returns the relational table schema with
--   the new fexp. If not, it doesn't return it.
--   Helper for linearizeSchema.
linearizeTableSch :: TableSchema -> [Opt RTableSchema]
linearizeTableSch = undefined


instance Variational Schema where
  type NonVariational Schema = Maybe RSchema 

  type Variant Schema = Opt RSchema

  configure = configSchema

  linearize = linearizeSchema

-- | The feature model associated with a schema.
featureModel :: Schema -> FeatureExpr
featureModel = getFexp

-- | Gets the structure of schema.
schemaStrct :: Schema -> Map Relation TableSchema
schemaStrct = getObj 

-- | Errors querying schema.
data SchemaError = MissingRelation Relation
                 | MissingAttribute Attribute
                 -- | InvalidConfig (Config Bool) FeatureExpr
                 | InvalidConfig FeatureExpr
  deriving (Data,Eq,Generic,Ord,Read,Show,Typeable)

instance Exception SchemaError

