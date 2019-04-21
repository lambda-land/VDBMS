-- | translates a vq to a list of opt vq.
module VDB.QueryTrans.VqToOptVq where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational

-- removes choices in vq and returns a list of 
-- opt vqs. note that the returned vq although
-- written in our algebra doesn't have choices.
removeChoiceInVq :: Algebra -> F.FeatureExpr -> [Opt Algebra]
removeChoiceInVq (SetOp s q1 q2) ctx = 
  combOpts F.And (SetOp s) optQ1 optQ2
    where
      optQ1 = removeChoiceInVq q1 ctx
      optQ2 = removeChoiceInVq q2 ctx
removeChoiceInVq (Proj as q) ctx = mapSnd (Proj as) optQs
  where 
    optQs = removeChoiceInVq q ctx
removeChoiceInVq (Sel c q) ctx = 
  combOpts F.And Sel cs optQs
  where
    cs = removeChoiceInCond c ctx
    optQs = removeChoiceInVq q ctx
removeChoiceInVq (AChc f q1 q2) ctx = optQ1 ++ optQ2
  where
    optQ1 = removeChoiceInVq q1 $ F.And f ctx
    optQ2 = removeChoiceInVq q2 $ F.And (F.Not f) ctx
removeChoiceInVq other ctx = [mkOpt ctx other]
-- removeChoice other ctx = [mkOpt other ctx]
-- removeChoice Empty = undefined

-- removes choices from conditions.
removeChoiceInCond :: C.Condition -> F.FeatureExpr -> [Opt C.Condition]
removeChoiceInCond (C.Not c) ctx = mapSnd (C.Not) optCs
  where
    optCs = removeChoiceInCond c ctx
removeChoiceInCond (C.Or c1 c2) ctx = combOpts F.And C.Or optC1 optC2 
  where
    optC1 = removeChoiceInCond c1 ctx
    optC2 = removeChoiceInCond c2 ctx
removeChoiceInCond (C.And c1 c2) ctx = combOpts F.And C.And optC1 optC2 
  where
    optC1 = removeChoiceInCond c1 ctx
    optC2 = removeChoiceInCond c2 ctx
removeChoiceInCond (C.CChc f c1 c2) ctx = optC1 ++ optC2
  where 
    optC1 = removeChoiceInCond c1 ctx
    optC2 = removeChoiceInCond c2 ctx
removeChoiceInCond other ctx = [mkOpt ctx other]


