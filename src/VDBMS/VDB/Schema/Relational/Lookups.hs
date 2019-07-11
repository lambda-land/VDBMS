-- | Relational database schema look up operations.
module VDBMS.VDB.Schema.Relational.Lookups (

        lookupRelation,
        lookupAttrType

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Monad.Catch

import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Type (SqlType)

lookupRelation :: MonadThrow m => Relation -> RSchema -> m RTableSchema
lookupRelation r s = maybe (throwM $ RMissingRelation r) return $ M.lookup r s

lookupAttrType :: MonadThrow m => Attribute -> RTableSchema -> m SqlType
lookupAttrType a t = maybe (throwM $ RMissingAttribute a) return $ M.lookup a t

