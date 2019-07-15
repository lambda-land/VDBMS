-- | Variational database schema apply feature expression operations.
module VDBMS.VDB.Schema.ApplyFexp (

        appFexpTableSch,
        appFexpRowType

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import VDBMS.VDB.Schema.Types
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.Variational.Opt
import VDBMS.Features.SAT (satisfiable)

import Control.Monad.Catch (throwM, MonadThrow)

-- | applying a feature expression to table schema and 
--   and dropping the attributes that shouldn't be present anymore.
--   i.e. their pres cond is unsatisfiable.
appFexpTableSch :: MonadThrow m => FeatureExpr -> TableSchema -> m TableSchema
appFexpTableSch f t
    | satisfiable f' = return $ mkOpt f' $ appFexpRowType f t
    | otherwise = throwM $ InconsistentFexpWithTableSch f t
    	-- error $ "applying the fexp " ++ show f ++ "to table schema results in an invalid table schema!!"
  where 
    f' = shrinkFeatureExpr (And f $ getFexp t)

-- | applies a feature expression to a table schema and returns a row type.
--   note that it doesn't apply the fexp to the attributes.
--   it just filters the attributes without updating their pres cond.
--   since the fexp is being conjoined with the table pres cond and
--   that would propagate to attributes too so we don't actually 
--   need to update attribute's pres cond.
appFexpRowType :: FeatureExpr -> TableSchema -> RowType
appFexpRowType f t = M.filter (\(f',_) -> satisfiable (And (And f f') $ getFexp t)) $ getObj t
