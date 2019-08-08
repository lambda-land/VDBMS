-- | Variation minimization of variational relational queries.
module VDBMS.QueryLang.RelAlg.Variational.Minimization where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
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
appFexpOptAtts :: F.FeatureExpr -> OptAttributes -> OptAttributes
appFexpOptAtts f = mapFst (F.And f) 

-- | Choice distributive laws.
chcDistr :: Algebra -> Algebra
chcDistr (AChc f (Proj l1 rq1) (Proj l2 rq2)) 
  = Proj (appFexpOptAtts f l1 ++ appFexpOptAtts (F.Not f) l2) 
         (Rename Nothing (Prod rq1 rq2))
chcDistr (AChc f (Sel c1 rq1) (Sel c2 rq2))
  = Sel (VsqlCChc f c1 c2) 
        (Rename Nothing (AChc f (thing rq1) (thing rq2)))
chcDistr (AChc f (Prod rq1 rq2) (Prod rq3 rq4)) 
  = Prod (Rename Nothing (AChc f (thing rq1) (thing rq3))) 
         (Rename Nothing (AChc f (thing rq2) (thing rq4)))
chcDistr (AChc f (Join rq1 rq2 c1) (Join rq3 rq4 c2))
  = Join (Rename Nothing (AChc f (thing rq1) (thing rq3))) 
         (Rename Nothing (AChc f (thing rq2) (thing rq4))) 
         (CChc f c1 c2)
chcDistr (AChc f (SetOp Union q1 q2) (SetOp Union q3 q4))
  = SetOp Union (AChc f q1 q3) (AChc f q2 q4)

-- | Pushes out projection as far as possible.
pushOutProj :: Algebra -> Algebra
pushOutProj (Sel c (Rename Nothing (Proj as rq))) = Proj as (Rename Nothing (Sel c rq))
pushOutProj (Proj as1 (Rename Nothing (Proj as2 rq))) = Proj as1 rq 

-- | relational alg rules.
relEq :: Algebra -> Algebra
-- question: how to extract all selections from inner queries?
relEq (Sel c1 (Rename Nothing (Sel c2 rq))) = Sel (VsqlAnd c1 c2) rq 

-- | choices rules.

-- | relational alg and choices combined rules.
chcRel :: Algebra -> Algebra
chcRel (AChc f (Sel (VsqlCond (And c1 c2)) rq1) (Sel (VsqlCond (And c3 c4)) rq2)) = undefined
chcRel (AChc f (Sel (VsqlAnd (VsqlCond c1) (VsqlCond c2)) rq1) (Sel (VsqlAnd (VsqlCond c3) (VsqlCond c4)) rq2)) = undefined
-- chcRel 








