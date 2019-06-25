-- | the commuting diagram for type of vqs.
module VDBMS.TypeSystem.Properties (

        typeCommutingDiagram

) where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Schema.Schema
import VDBMS.Features.Config
import VDBMS.TypeSystem.TypeSystem

-- | check commuting diagram for type system.
typeCommutingDiagram :: [Config Bool] -> VariationalContext -> Schema -> Algebra -> Bool
typeCommutingDiagram cs ctx s vq = undefined
  -- foldr (&&) True (map (typeDiagram_c ctx s vq) cs)
  -- where
  --   typeDiagram_c ctx s vq c = case (vEnv,env_c) of
  --     (Just env, Just envc) -> vEnv_c == envc
  --       where vEnv_c = configureTypeEnv env c
  --     (Nothing, _) -> error "the vq isn't type correct!"
  --     (Just _, Nothing) -> error "sth went terribly wrong when checking type diagram!!"
  --     where 
  --       vEnv = typeOfVquery' vq ctx s 
  --       q_c = configure vq c 
  --       env_c = typeOfVquery' q_c (Lit True) s 

-- | applies a config to a type env.
configureTypeEnv :: TypeEnv' -> Config Bool -> TypeEnv'
configureTypeEnv = flip appConfRowType' 


