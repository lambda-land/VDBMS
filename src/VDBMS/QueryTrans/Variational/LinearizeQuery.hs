-- | linearizes variational queries.
module VDBMS.QueryTrans.Variational.LinearizeQuery (

        linearize

) where 

import VDBMS.QueryLang.Variational.Algebra
import VDBMS.QueryLang.Relational.Algebra
-- import VDBMS.Features.Config
import VDBMS.Variational.Opt
-- import VDBMS.Variational.Variational
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import qualified VDBMS.QueryLang.Variational.Condition as C
import VDBMS.QueryLang.Relational.Condition

-- | Linearizes variational conditions to a list of opt relational conditions.
linearizeCond :: C.Condition -> [Opt RCondition]
linearizeCond (C.Lit b)        = pure $ mkOpt (F.Lit True) (RLit b)
linearizeCond (C.Comp c a1 a2) = pure $ mkOpt (F.Lit True) (RComp c a1 a2)
linearizeCond (C.Not c)        = mapSnd RNot $ linearizeCond c
linearizeCond (C.Or c1 c2)     = combOpts F.And ROr (linearizeCond c1) (linearizeCond c2)
linearizeCond (C.And c1 c2)    = combOpts F.And RAnd (linearizeCond c1) (linearizeCond c2)
linearizeCond (C.CChc f c1 c2) = mapFst (F.And f) (linearizeCond c1) ++
                                 mapFst (F.And (F.Not f)) (linearizeCond c2)

-- | Linearizes a variational query to a list of opt relational queries.
linearize :: Algebra -> [Opt RAlgebra]
linearize (SetOp s q1 q2) = combOpts F.And (RSetOp s) (linearize q1) (linearize q2)
linearize (Proj as q)     = combOpts F.And RProj (groupOpts as) (linearize q)
linearize (Sel c q)       = combOpts F.And RSel (linearizeCond c) (linearize q)
linearize (AChc f q1 q2)  = mapFst (F.And f) (linearize q1) ++
                            mapFst (F.And (F.Not f)) (linearize q2)
linearize (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
linearize Empty           = pure $ mkOpt (F.Lit True) REmpty