-- | Variational database schema look up operations.
module VDBMS.VDB.Schema.Variational.Lookups (

        lookupAttFexpInRowType,
        lookupAttFexpTypeInRowType,
        lookupTableSch,
        lookupRelationFexp,
        lookupRel,
        lookupRelAttsList,
        lookupAttType,
        lookupAttFexp

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Monad.Catch

import VDBMS.VDB.Schema.Variational.Types
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
import VDBMS.Variational.Opt
import VDBMS.DBMS.Value.Value (SqlType)

-- | gets the attribute fexp conjoind with the table pres cond
--   from a table schema
-- lookupAttFexpInTableSch :: Attribute -> TableSchema -> Maybe FeatureExpr
-- lookupAttFexpInTableSch a (tf,tr) = case M.lookup a tr of 
--                                Just (f,_) 
--                                  | satisfiable f' -> Just f'
--                                  | otherwise -> Nothing
--                                    where f' = And tf f
--                                _ -> Nothing

-- -- | gets the attribute pres cond conjoined with the table pres cond
-- --   and the attribute type from a table schema.
-- lookupAttFexpTypeInTableSch :: Attribute -> TableSchema -> Maybe (Opt SqlType)
-- lookupAttFexpTypeInTableSch a (tf,tr) = case M.lookup a tr of 
--                                           Just (f,t)
--                                             | satisfiable f' -> Just (f',t)
--                                             | otherwise -> Nothing
--                                               where f' = And tf f 
--                                           _ -> Nothing

-- | get the attribute fexp from a rowtype
lookupAttFexpInRowType :: MonadThrow m => Attribute -> RowType -> m FeatureExpr
lookupAttFexpInRowType a r = 
  maybe (throwM $ MissingAttribute a) (return . fst) $ M.lookup a r
  
-- | Get the fexp and type of an attribute in a rowtype
lookupAttFexpTypeInRowType :: MonadThrow m => Attribute -> RowType 
                                           -> m (Opt SqlType)
lookupAttFexpTypeInRowType a r = 
  maybe (throwM $ MissingAttribute a) return $ M.lookup a r

-- | Get the schema of a relation in the database, where 
-- 	the relation schema is stored as a row type.
lookupTableSch :: MonadThrow m => Relation -> Schema -> m TableSchema
lookupTableSch r (_,m) = maybe (throwM $ MissingRelation r) return $ M.lookup r m

-- | Get the feature expression of a relation in a database.
lookupRelationFexp :: MonadThrow m => Relation -> Schema -> m FeatureExpr
lookupRelationFexp r s = lookupTableSch r s >>= return . fst

-- | Get the row type of a relation in a database.
lookupRel :: MonadThrow m => Relation -> Schema -> m RowType
lookupRel r s = lookupTableSch r s >>= return . snd

-- | get the attributes of a relation in a database.
lookupRelAttsList :: MonadThrow m => Relation -> Schema -> m [Attribute]
lookupRelAttsList r s = M.keys <$> lookupRel r s

-- | Get the type and feature exp of an attribute in a database.
lookupAttribute :: MonadThrow m => Attribute -> Relation -> Schema 
                                -> m (Opt SqlType)
lookupAttribute a r s = lookupRel r s >>= lookupAttFexpTypeInRowType a

-- | Get the type of an attribute in a database.
lookupAttType :: MonadThrow m => Attribute -> Relation -> Schema -> m SqlType
lookupAttType a r s = lookupAttribute a r s >>= return . snd

-- | Get the feature expression of an attribute in adatabase.
lookupAttFexp :: MonadThrow m => Attribute -> Relation -> Schema -> m FeatureExpr
lookupAttFexp a r s = lookupAttribute a r s >>= return . fst
