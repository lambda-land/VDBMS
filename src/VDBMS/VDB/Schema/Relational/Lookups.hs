-- | Relational database schema look up operations.
module VDBMS.VDB.Schema.Relational.Lookups (

        rlookupRelation
        , rlookupAttrType
        , rlookupAttsList

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Monad.Catch

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Type (SqlType)

rlookupRelation :: MonadThrow m => Relation -> RSchema -> m RTableSchema
rlookupRelation r s = maybe (throwM $ RMissingRelation r) return $ M.lookup r s

rlookupAttrType :: MonadThrow m => Attribute -> RTableSchema -> m SqlType
rlookupAttrType a t = maybe (throwM $ RMissingAttribute a) return $ M.lookup a t

rlookupAttsList :: MonadThrow m => Relation -> RSchema -> m [Attribute]
rlookupAttsList r s = M.keys <$> rlookupRelation r s