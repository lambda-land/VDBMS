-- timing parts of the system.
module VDBMS.TypeSystem.Variational.RunTypeQuery where 

import VDBMS.QueryGen.VRA.PushSchToQ 
import VDBMS.TypeSystem.Variational.TypeSystem (simplType, TypeEnv, typeOfQuery, applyFuncToAttFexp)
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
numUniqVarPushedSchQ s q = numUniqueVariantQ s (pushSchToQ s q)


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
