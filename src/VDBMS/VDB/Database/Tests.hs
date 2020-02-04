-- | Database tests.
module VDBMS.VDB.Database.Tests (

       DatabaseErr(..)
       , isVDBvalid

) where

-- import VDBMS.Features.Config
-- import VDBMS.Features.ConfFexp
-- import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.DBMS.Table.Table (SqlRow, SqlTable, lookupAttValInSqlRow)
import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.VDB.Name 
import VDBMS.Features.SAT (satisfiable, unsatisfiable)
-- import VDBMS.VDB.Schema.Variational.Tests (isVschValid)
import VDBMS.VDB.Schema.Variational.Schema 

import Database.HDBC (SqlValue(..))

import Control.Monad.Catch 
import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Control.Monad (foldM)
import Data.Maybe (fromJust)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Bitraversable (bitraverse, bimapDefault)

-- | Errors for database validity tests.
data DatabaseErr
  = UnsatTuple Relation FeatureExpr SqlRow 
  | UnsatPCWithoutNullValue Relation Attribute FeatureExpr SqlValue
  deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception DatabaseErr

-- | checks: 1) vschema is valid
--   2) all tuples have satisfiable pc
--   3) when unsat (fm and pc_r and pc_a and pc_tuple)
--      the tuple value is null
isVDBvalid :: (Database conn, MonadThrow m, MonadIO m) => conn -> m Bool
isVDBvalid conn = 
  do isVschValid (schema conn) 
     areTablesValid conn
     areValuesValid conn

-- | checks if a tuple's pc is valid.
--   assumption: tuples have pc attribute.
-- for a given t ∈r. sat (fm ∧ pcᵣ ∧ pc\_t )
isTupleValid :: MonadThrow m => PCatt -> Relation -> FeatureExpr 
                             -> SqlRow -> m Bool
isTupleValid pc r f t 
  | satisfiable t_pc = return True
  | otherwise = throwM $ UnsatTuple r t_pc t
    where 
      t_pc = (And f ((sqlval2fexp . fromJust) $ M.lookup (attributeName pc) t))

-- | checks if all tuples of a relation are valid.
-- ∀t ∈ r. sat (fm ∧ pcᵣ ∧ pc\_t )
isTableValid :: MonadThrow m => PCatt -> Relation -> FeatureExpr
                             -> SqlTable -> m Bool
isTableValid pc r f = foldM 
  (\b t -> isTupleValid pc r f t >>= return . ((&&) b)) 
  True 

-- | checks if all tuples of all relations in the schema are valid.
-- ∀t ∈ r ∀r ∈ S. sat (fm ∧ pcᵣ ∧ pc\_t )
areTablesValid :: (Database conn, MonadThrow m, MonadIO m) => conn -> m Bool
areTablesValid conn = 
  do let sch = schema conn
         q :: String
         q = "SELECT * FROM "
         pc = presCond conn
         rels = schemaRels sch 
         -- gen :: MonadThrow m => Relation -> m ((Relation, FeatureExpr),String)
         gen r = do r_pc <- lookupRelationFexp r sch
                    return ((r, r_pc), q ++ relationName r ++ ";")
     rfqs <- mapM gen rels
     let runQ :: ((Relation, FeatureExpr), String) 
              -> IO ((Relation, FeatureExpr), SqlTable)
         runQ ((r,f),sql) = bitraverse (return . id) 
                                       (fetchQRows conn) 
                                       ((r,f),sql)
     rfts <- liftIO $ mapM runQ rfqs
     foldM (\b ((r,f),t) -> isTableValid pc r f t 
                        >>= return . ((&&) b)) 
           True 
           rfts

-- | checks that if unsat (fm ∧ pcᵣ ∧ pcₐ ∧ pc\_t) then
--   the value of attribute a in a tuple t is null.
-- for a given attribute and tuple ∈ r s.t.
-- unsat (fm ∧ pcᵣ ∧ pcₐ ∧ pc\_t). the value of attribute in tuple is null.
-- note that the fexp f that you're passing should be: f = fm ∧ pcᵣ ∧ pcₐ 
doesUnsatPcHaveNullValue_attr :: MonadThrow m => PCatt -> Relation -> Attribute 
                                              -> FeatureExpr -> SqlRow
                                              -> m Bool
doesUnsatPcHaveNullValue_attr pc r a f t = 
  do t_pc <- lookupAttValInSqlRow pc r t 
     let v_pc = And f (sqlval2fexp t_pc)
     val <- lookupAttValInSqlRow a r t 
     (case (unsatisfiable v_pc, val) of 
       (True, SqlNull) -> return True
       (True, _) -> throwM $ UnsatPCWithoutNullValue r a v_pc val 
       _ -> return True)

-- | checks if all unsat pcs of an attribute in a table 
--   have null values.
-- for a given attribute and ∀ tuple ∈ r s.t.
-- unsat (fm ∧ pcᵣ ∧ pcₐ ∧ pc\_t). the value of attribute in tuple is null.
doUnsatPcsHaveNullValues_attr :: MonadThrow m => PCatt -> Relation -> Attribute
                                              -> FeatureExpr -> SqlTable
                                              -> m Bool
doUnsatPcsHaveNullValues_attr pc r a f t = foldM 
  (\b tuple -> doesUnsatPcHaveNullValue_attr pc r a f tuple 
           >>= return . ((&&) b)) 
  True 
  t 

-- | checks all unsat pcs of all attributes in a table
--   have null values.
-- ∀ attribute and ∀ tuple ∈ r s.t.
-- unsat (fm ∧ pcᵣ ∧ pcₐ ∧ pc\_t). the value of attribute in tuple is null.
doUnsatPcsHaveNullValues_rel :: MonadThrow m => PCatt -> Schema -> Relation
                                             -> SqlTable
                                             -> m Bool
doUnsatPcsHaveNullValues_rel pc s r t = 
  do atts <- lookupRelAttsList r s
     let pairAttPc :: MonadThrow m => Relation -> Schema -> Attribute 
                                   ->  m (Attribute, FeatureExpr)
         pairAttPc rel sch a = lookupAttFexp a rel sch 
           >>= return . (\atPC -> (a, atPC))
     afs <- mapM (pairAttPc r s) atts
     foldM 
       (\b (att,att_pc) -> doUnsatPcsHaveNullValues_attr pc r att att_pc t 
                       >>= return . ((&&) b)) 
       True 
       afs

-- | checks all unsat pcs of all attributes in tables 
--   for all tables of a database they have null values.
-- ∀a ∈r, ∀ r ∈ S, unsat(fm ∧ pcᵣ ∧ pcₐ ∧ pc\_t) then val(a) = null. 
areValuesValid :: (Database conn, MonadThrow m, MonadIO m) => conn -> m Bool
areValuesValid conn = 
  do let sch = schema conn 
         pc = presCond conn
         q :: String
         q = "SELECT * FROM "
         rels = schemaRels sch 
         rqs = map (\r -> (r, q ++ relationName r ++ ";")) rels
         runQ :: (Relation, String) -> IO (Relation, SqlTable)
         runQ = bitraverse (return . id) (fetchQRows conn) 
     rts <- liftIO $ mapM runQ rqs
     foldM (\b (r,t) -> doUnsatPcsHaveNullValues_rel pc sch r t 
                    >>= return . ((&&) b))
           True
           rts


