-- | Configuration semantics of vquery. 
module VDBMS.QueryLang.Variational.ConfigQuery (

        configureVquery

) where 

import VDBMS.QueryLang.Variational.Algebra
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

