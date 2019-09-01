-- | Relational database schema look up operations.
module VDBMS.VDB.Schema.Relational.Lookups (

        rlookupRelation
        , rlookupAttrType
        , rlookupAttsList

) where

-- import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Monad.Catch

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Type (SqlType)

-- | lookups the table schema of a relation from a schema.
rlookupRelation :: MonadThrow m => Relation -> RSchema -> m RTableSchema
rlookupRelation r s = maybe (throwM $ RMissingRelation r) return $ M.lookup r s

-- | lookups the sqltype of an attribute from a table schema.
rlookupAttrType :: MonadThrow m => Attribute -> RTableSchema -> m SqlType
rlookupAttrType a t = maybe (throwM $ RMissingAttribute a) return $ M.lookup a t

-- | lookups the attribute list of a relation from a schema.
rlookupAttsList :: MonadThrow m => Relation -> RSchema -> m [Attribute]
rlookupAttsList r s = M.keys <$> rlookupRelation r s