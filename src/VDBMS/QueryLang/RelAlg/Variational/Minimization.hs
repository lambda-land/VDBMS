-- | Variation minimization of variational relational queries.
module VDBMS.QueryLang.RelAlg.Variational.Minimization where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
-- import VDBMS.Features.Config
-- import VDBMS.QueryLang.ConfigQuery
import VDBMS.Variational.Opt (mapFst, getObj)
-- import VDBMS.Variational.Variational

import Data.Maybe (isNothing)

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
-- Note that you don't necessarily want to push out all projs.
-- Eg: proj l1 R * proj l2 S = proj (l1 + l2) (R * S)
--     but the rhs isn't more efficient than the lhs! keep in 
--     min that the same goes for joins.
-- There are also cases that you CANNOT push out projs:
-- Eg: proj l1 q1 `union` proj l1 q2 <> proj l1 (q1 `union` q2)
-- TODO: you haven't consider the possibility of renaming attributes.
--       it may screw up some of the rules. GO OVER THEM AGAIN!!
pushOutProj :: Algebra -> Algebra
pushOutProj (SetOp o q1 q2)
  = SetOp o (pushOutProj q1) (pushOutProj q2)
pushOutProj (AChc f q1 q2) 
  = AChc f (pushOutProj q1) (pushOutProj q2)
pushOutProj (Join rq1 rq2 c)
  = Join (renameMap pushOutProj rq1) (renameMap pushOutProj rq2) c
pushOutProj (Prod rq1 rq2) 
  = Prod (renameMap pushOutProj rq1) (renameMap pushOutProj rq2)
pushOutProj (Sel c (Rename Nothing (Proj as rq)))
  = Proj as (Rename Nothing (Sel c (renameMap pushOutProj rq)))
pushOutProj (Proj as1 (Rename Nothing (Proj as2 rq)))
  = Proj as1 (renameMap pushOutProj rq)

-- | checks if a sql condition is of the form "attr in query" condition.
notInCond :: VsqlCond -> Bool 
notInCond (VsqlIn _ _)     = True
notInCond (VsqlCond _)     = False
notInCond (VsqlNot c)      = notInCond c
notInCond (VsqlOr l r)     = notInCond l && notInCond r
notInCond (VsqlAnd l r)    = notInCond l && notInCond r 
notInCond (VsqlCChc _ l r) = notInCond l && notInCond r 

-- | knowing that the sql condition is not of the form "attr in query"
--   converts the sql condition to a relational condition.
relCond :: VsqlCond -> Condition
relCond (VsqlCond c)     = c 
relCond (VsqlIn _ _)     = error $ "didn't expect to get a condition of the form attr in query!! QUERY VAR MIN!!"
relCond (VsqlNot c)      = Not (relCond c)
relCond (VsqlOr l r)     = Or (relCond l) (relCond r)
relCond (VsqlAnd l r)    = And (relCond l) (relCond r)
relCond (VsqlCChc f l r) = CChc f (relCond l) (relCond r)

-- | optimizes the selection queries.
optSel :: Algebra -> Algebra
optSel (Sel c1 (Rename Nothing (Sel c2 rq))) 
  = Sel (VsqlAnd c1 c2) (renameMap optSel rq)
optSel q@(Sel c1 (Rename Nothing (Proj as (Rename n (Sel c2 rq)))))
  | noAttRename as = Proj as (Rename n (Sel (VsqlAnd c1 c2) (renameMap optSel rq)))
  | otherwise      = q
    where
      noAttRename :: OptAttributes -> Bool
      noAttRename as = and $ fmap (isNothing . name . getObj) as
optSel q@(Sel c (Rename Nothing (Prod rq1 rq2)))
  | notInCond c = Join (renameMap optSel rq1) (renameMap optSel rq2) (relCond c)
  | otherwise   = q 
optSel q@(Sel c1 (Rename Nothing (Join rq1 rq2 c2)))
  | notInCond c1 = Join rq1 rq2 (And (relCond c1) c2)
  | otherwise    = q


-- | choices rules.

-- | relational alg and choices combined rules.
chcRel :: Algebra -> Algebra
chcRel (AChc f (Sel (VsqlCond (And c1 c2)) rq1) (Sel (VsqlCond (And c3 c4)) rq2)) = undefined
chcRel (AChc f (Sel (VsqlAnd (VsqlCond c1) (VsqlCond c2)) rq1) (Sel (VsqlAnd (VsqlCond c3) (VsqlCond c4)) rq2)) = undefined
-- chcRel 








