-- timing parts of the system.
module VDBMS.TypeSystem.Variational.RunTypeQuery where 

import VDBMS.QueryGen.VRA.PushSchToQ 
import VDBMS.TypeSystem.Variational.TypeSystem (TypeEnv, typeOfQuery, applyFuncToAttFexp)
import VDBMS.VDB.Schema.Variational.Schema (Schema, featureModel)
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Features.FeatureExpr.FeatureExpr 
import VDBMS.Variational.Opt

import Control.Monad.Catch
import qualified Data.Map as M 
import qualified Data.Map.Strict as SM

-- | runs the typeofquery for a given query and schema,
--   initiating tbe context to the feature model.
runTypeQuery :: MonadThrow m => Algebra -> Schema -> m TypeEnv
runTypeQuery q s = typeOfQuery q (featureModel s) s

-- | Simplifies the type of a query.
simplType :: MonadThrow m => Algebra -> Schema -> m TypeEnv
simplType q s = 
  do t <- runTypeQuery q s
     let shrinkType :: TypeEnv -> TypeEnv
         shrinkType env = applyFuncFexp shrinkFeatureExpr 
           $ applyFuncObj (SM.map (applyFuncToAttFexp shrinkFeatureExpr)) env 
     return $ shrinkType t


-- | simpilifies a type after type checking the query after
--   pushing the schema onto it.
simplTypeWithPushSch :: MonadThrow m => Algebra -> Schema -> m TypeEnv
simplTypeWithPushSch q s = 
  do let q' = pushSchToQ s q
     simplType q' s

