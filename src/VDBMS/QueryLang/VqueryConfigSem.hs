-- | Configuration semantics of vquery. 
module VDBMS.QueryLang.VqueryConfigSem (

        configureVquery

) where 

import VDBMS.QueryLang.Algebra
import VDBMS.Features.Config
import VDBMS.Variational.Opt
import VDBMS.Variational.Variational

-- | given a vquery and a configuration returns
--   the pure relational query for that configuration.
configureVquery :: Algebra -> Config Bool -> Algebra 
configureVquery (SetOp o l r)  c = SetOp o (configureVquery l c) (configureVquery r c) 
configureVquery (Proj as q)    c = Proj (configureOptListRetOpt c as) (configureVquery q c)
configureVquery (Sel cond q)   c = Sel (configure c cond) (configureVquery q c)
configureVquery q@(AChc _ _ _) c = configureVquery (configure c q) c
configureVquery (TRef r)       _ = TRef r
configureVquery Empty          _ = Empty

-- Issues:
-- * equivalency of queries (and confedQs) is wrong!
-- * you should move equivVqs to some test file.


-- | checks whether two configured queries are equivalent or not.
--   need to rewrite this! because == won't cut it!
equivConfedQs :: Algebra -> Algebra -> Bool
equivConfedQs = (==)

-- | checks commuting diagram for a variaitonal query.
equivVqs :: [Config Bool] -> Algebra -> Algebra -> Bool
equivVqs cs q q' = and $ zipWith equivConfedQs confq confq'
  where 
    confq  = map (configureVquery q) cs
    confq' = map (configureVquery q') cs 


