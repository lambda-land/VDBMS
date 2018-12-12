-- configuration semantics of vquery. 
module VDB.VqueryConfigSem where 

import VDB.Algebra
import VDB.Variational
import VDB.Config

-- | given a vquery and a configuration returns
--   the pure relational query for that configuration.
configureVquery :: Algebra -> Config Bool -> Algebra 
configureVquery (SetOp o l r)  c = SetOp o (configureVquery l c) (configureVquery r c) 
configureVquery (Proj as q)    c = Proj (configureOptListRetOpt c as) (configureVquery q c)
configureVquery (Sel cond q)   c = Sel (configure c cond) (configureVquery q c)
configureVquery q@(AChc _ _ _) c = configureVquery (configure c q) c
configureVquery (TRef r)       _ = TRef r
configureVquery Empty          _ = Empty
 -- = flip configure


-- test query
-- vqtest :: Algebra
-- vqtest = Proj [(Ref "A", "A1"), (Lit True, "A2")] (TRef "R1")

-- conf1 :: Config Bool
-- conf1 "A" = True

-- configureVquery vqtest conf1
-- ===>
-- Proj [(TRUE,Attribute {attributeName = "A1"}),(TRUE,Attribute {attributeName = "A2"})] 
--      (TRef (Relation {relationName = "R1"}))