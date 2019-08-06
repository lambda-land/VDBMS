-- | Variation minimization of variational relational queries.
module VDBMS.QueryLang.RelAlg.Variational.Minimization where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
-- import VDBMS.Features.Config
-- import VDBMS.QueryLang.ConfigQuery
import VDBMS.Variational.Opt (mapFst)
-- import VDBMS.Variational.Variational

-- | Applies the minimization rules until the query doesn't change.
appMin :: Algebra -> Algebra
appMin q 
  | minVar q == q = q 
  | otherwise = appMin (minVar q)

-- | Variation minimization rules.
-- Note: not sure which side is more optimized. We can determine that by
--       running some experiments. It also probably depends on the 
--       approach we take.
minVar :: Algebra -> Algebra 
minVar = undefined

-- | Applies a feature expression to all attributes in an opt attrs.
appFexpOptAtts :: FeatureExpr -> OptAttributes -> OptAttributes
appFexpOptAtts f = mapFst (And f) 

-- | Choice distributive laws.
chcDistr :: Algebra -> Algebra
chcDistr (AChc f (Proj l1 rq1) (Proj l2 rq2)) 
  = Proj (appFexpOptAtts f l1 ++ appFexpOptAtts (Not f) l2) (Rename Nothing (Prod rq1 rq2))
-- chcDistr (AChc f (Sel c1 rq1) (Sel c2 rq2))
--   = Sel (VsqlCChc f c1 c2) (AChc f rq1 rq2)
-- chcDistr (AChc f (Prod rq1 rq2) (Prod rq3 rq4)) 
--   = Prod (AChc f rq1 rq3) (AChc f rq2 rq4)
-- chcDistr (AChc f (Join rq1 rq2 c1) (Join rq3 rq4 c2))
--   = Join (AChc f rq1 rq3) (AChc f rq2 rq4) (VsqlCChc f (VsqlCond c1) (VsqlCond c2))
chcDistr (AChc f (SetOp Union q1 q2) (SetOp Union q3 q4))
  = SetOp Union (AChc f q1 q3) (AChc f q2 q4)