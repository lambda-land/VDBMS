-- timing parts of the system.
module VDBMS.TypeSystem.Variational.RunTypeQuery where 

import VDBMS.QueryGen.VRA.PushSchToQ 
import VDBMS.TypeSystem.Variational.TypeSystem (TypeEnv, typeOfQuery, applyFuncToAttFexp)
import VDBMS.VDB.Schema.Variational.Schema (Schema, featureModel)
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra, numVariantQ, numUniqueVariantQ)
import VDBMS.Features.FeatureExpr.FeatureExpr 
import VDBMS.Variational.Opt
import VDBMS.Features.Config (Config)

import Control.Monad.Catch
-- import qualified Data.Map as M 
import qualified Data.Map.Strict as SM

-- |
numVariantPushedSchQ :: Schema -> [Config Bool] -> Algebra -> Int 
numVariantPushedSchQ s cs q = numVariantQ (pushSchToQ s q) cs

-- |
numUniqVarPushedSchQ :: Schema -> Algebra -> Int 
numUniqVarPushedSchQ s q = numUniqueVariantQ (pushSchToQ s q)

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

-- |checks if a query is type correct or not. 
checkType :: MonadThrow m => Algebra -> Schema -> m ()
checkType q s = simplType q s >> return ()


-- NOTE: don't need the following two functions since
-- the query is type checked first and then the schema
-- is pushed onto it.
-- | simpilifies a type after type checking the query after
--   pushing the schema onto it.
simplTypeWithPushSch :: MonadThrow m => Algebra -> Schema -> m TypeEnv
simplTypeWithPushSch q s = 
  do let q' = pushSchToQ s q
     simplType q' s

-- |checks if a query (after pushing schema onto it) is type correct or not. 
checkTypeWithPushSch :: MonadThrow m => Algebra -> Schema -> m ()
checkTypeWithPushSch q s = simplTypeWithPushSch q s >> return ()
