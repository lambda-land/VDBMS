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

-- | get the attribute fexp from a rowtype
-- lookupAttFexpInRowType :: MonadThrow m => Attribute -> RowType -> m FeatureExpr
-- lookupAttFexpInRowType a r = 
--   maybe (throwM $ MissingAttribute a) (return . fst) $ M.lookup a r
  
-- -- | Get the fexp and type of an attribute in a rowtype
-- lookupAttFexpTypeInRowType :: MonadThrow m => Attribute -> RowType 
--                                            -> m (Opt SqlType)
-- lookupAttFexpTypeInRowType a r = 
--   maybe (throwM $ MissingAttribute a) return $ M.lookup a r

-- -- | Get the schema of a relation in the database, where 
-- -- 	the relation schema is stored as a row type.
-- lookupRowType :: MonadThrow m => Relation -> Schema -> m TableSchema
-- lookupRowType r (_,m) = maybe (throwM $ MissingRelation r) return $ M.lookup r m

-- -- | Get the feature expression of a relation in a database.
-- lookupRelationFexp :: MonadThrow m => Relation -> Schema -> m FeatureExpr
-- lookupRelationFexp r s = lookupRowType r s >>= return . fst

-- -- | Get the row type of a relation in a database.
-- lookupRel :: MonadThrow m => Relation -> Schema -> m RowType
-- lookupRel r s = lookupRowType r s >>= return . snd

-- -- | get the attributes of a relation in a database.
-- lookupRelAttsList :: MonadThrow m => Relation -> Schema -> m [Attribute]
-- lookupRelAttsList r s = M.keys <$> lookupRel r s

-- -- | Get the type and feature exp of an attribute in a database.
-- lookupAttribute :: MonadThrow m => Attribute -> Relation -> Schema 
--                                 -> m (Opt SqlType)
-- lookupAttribute a r s = lookupRel r s >>= lookupAttFexpTypeInRowType a

-- -- | Get the type of an attribute in a database.
-- lookupAttType :: MonadThrow m => Attribute -> Relation -> Schema -> m SqlType
-- lookupAttType a r s = lookupAttribute a r s >>= return . snd

-- -- | Get the feature expression of an attribute in adatabase.
-- lookupAttFexp :: MonadThrow m => Attribute -> Relation -> Schema -> m FeatureExpr
-- lookupAttFexp a r s = lookupAttribute a r s >>= return . fst
