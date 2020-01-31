-- | Database tests.
module VDBMS.VDB.Database.Tests where

-- import VDBMS.Features.Config
-- import VDBMS.Features.ConfFexp
-- import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.DBMS.Table.Table (SqlRow, SqlTable)
import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.VDB.Name 
import VDBMS.Features.SAT (satisfiable)
-- import VDBMS.VDB.Schema.Variational.Tests (isVschValid)
import VDBMS.VDB.Schema.Variational.Schema 

import Control.Monad.Catch 
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
  deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception DatabaseErr

-- | checks: 1) vschema is valid
--   2) all tuples have satisfiable pc
--   3) when unsat (fm and pc_r and pc_a and pc_tuple)
--      the tuple value is null
isVDBvalid :: (Database conn, MonadThrow m) => conn -> m Bool
isVDBvalid conn = 
  do isVschValid (schema conn) 
     areTablesValid conn
     return undefined


-- | checks if a tuple's pc is valid.
--   assumption: tuples have pc attribute.
isTupleValid :: MonadThrow m => PCatt -> Relation -> FeatureExpr 
                             -> SqlRow -> m Bool
isTupleValid pc r f t 
  | satisfiable t_pc = return True
  | otherwise = throwM $ UnsatTuple r t_pc t
    where 
      t_pc = (And f ((sqlval2fexp . fromJust) $ M.lookup (attributeName pc) t))

-- | checks if all tuples of a relation are valid.
isTableValid :: MonadThrow m => PCatt -> Relation -> FeatureExpr
                             -> SqlTable -> m Bool
isTableValid pc r f = foldM (\b t -> isTupleValid pc r f t >>= return . ((&&) b)) True 

-- | checks if all tuples of all relations in the schema are valid.
areTablesValid :: (Database conn, MonadThrow m) => conn -> m Bool
areTablesValid conn = 
  do let sch = schema conn
     --     -- fm = featureModel sch
     --     q :: String
     --     q = "SELECT * FROM "
     --     pc = presCond conn
     --     -- gen :: MonadThrow m => Relation -> m (Relation, FeatureExpr)
     --     gen r = do r_pc <- lookupRelationFexp r sch
     --                return ((r, r_pc), q ++ relationName r ++ ";")
     -- rfqs <- mapM gen (schemaRels sch)
     -- let runQ :: ((Relation, FeatureExpr), String) -> IO ((Relation, FeatureExpr), SqlTable)
     --     runQ ((r,f),sql) = bitraverse (return . id) (fetchQRows conn) ((r,f),sql)
     -- rfts <- mapM runQ rfqs
     -- (\((r,f),t) -> isTableValid pc r f t) rfts
     return undefined
         



