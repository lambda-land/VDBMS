-- | relational alg optimization rules.
module VDBMS.QueryLang.RelAlg.Relational.Optimization (

       appOpt

)where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import VDBMS.TypeSystem.Relational.TypeSystem
import VDBMS.VDB.Schema.Relational.Types
-- -- import VDBMS.Features.Config
-- -- import VDBMS.QueryLang.ConfigQuery
-- import VDBMS.Variational.Opt (mapFst, getObj, getFexp, applyFuncFexp, mkOpt)
-- -- import VDBMS.Variational.Variational

-- import qualified Data.Map as M 
import qualified Data.Map.Strict as SM (lookup)
import Data.Maybe (catMaybes, fromJust)
import Data.List (partition)

-- | Applies the minimization rules until the query doesn't change.
appOpt :: RAlgebra -> RSchema -> RAlgebra
appOpt q s
  | opts q s == q = q 
  | otherwise     = appOpt (opts q s) s

-- | Relational optimization rules.
opts :: RAlgebra -> RSchema -> RAlgebra 
opts q s = 
  prjRDistr (selRDistr ((optRSel . pushOutRProj) q) s) s

-- | Pushes out projection as far as possible.
-- Note that you don't necessarily want to push out all projs.
-- Eg: proj l1 R * proj l2 S = proj (l1 + l2) (R * S)
--     but the rhs isn't more efficient than the lhs! keep in 
--     min that the same goes for joins.
-- There are also cases that you CANNOT push out projs:
-- Eg: proj l1 q1 `union` proj l1 q2 <> proj l1 (q1 `union` q2)
pushOutRProj :: RAlgebra -> RAlgebra
-- σ c (π l q) ≡ π l (σ c q)
pushOutRProj (RSel c (Rename Nothing (RProj as rq)))
  = RProj as (Rename Nothing (RSel c (renameMap pushOutRProj rq)))
-- π l₁ (π l₂ q) ≡ π l₁ q
-- checks if renaming happened in l₂ and update 
-- l₁ appropriately! 
pushOutRProj (RProj as1 (Rename Nothing (RProj as2 rq)))
  = RProj (updateAtts as1 as2) (renameMap pushOutRProj rq)
    where
      updateAtts :: Attributes -> Attributes -> Attributes
      updateAtts orgs subs = [ compAtts a subs | a <- orgs]
      compAtts :: Rename Attr -> Attributes -> Rename Attr
      compAtts a as 
        | null attList = a 
        | otherwise = head attList 
          where attList = catMaybes [ compAtt a att | att <- as]
      compAtt :: Rename Attr -> Rename Attr -> Maybe (Rename Attr)
      compAtt a1 a2 
        | name a2 == Nothing 
            = Just (Rename (name a1) (thing a2))
        | name a2 /= Nothing 
          && (attributeName . attribute . thing) a1 == (fromJust (name a2))
            = Just a2
        | otherwise = Nothing
pushOutRProj (RSetOp o q1 q2)
  = RSetOp o (pushOutRProj q1) (pushOutRProj q2)
pushOutRProj (RJoin rq1 rq2 c)
  = RJoin (renameMap pushOutRProj rq1) (renameMap pushOutRProj rq2) c
pushOutRProj (RProd rq1 rq2) 
  = RProd (renameMap pushOutRProj rq1) (renameMap pushOutRProj rq2)
pushOutRProj q = q 

-- | checks if a sql condition is of the form "attr in query" condition.
notInCond :: SqlCond RAlgebra -> Bool 
notInCond (SqlIn _ _)     = True
notInCond (SqlCond _)     = False
notInCond (SqlNot c)      = notInCond c
notInCond (SqlOr l r)     = notInCond l && notInCond r
notInCond (SqlAnd l r)    = notInCond l && notInCond r 

-- | knowing that the sql condition is not of the form "attr in query"
--   converts the sql condition to a relational condition.
relCond :: SqlCond RAlgebra -> RCondition
relCond (SqlCond c)     = c 
relCond (SqlIn _ _)     = error $ "didn't expect to get a condition of the form attr in query!! QUERY VAR MIN!!"
relCond (SqlNot c)      = RNot (relCond c)
relCond (SqlOr l r)     = ROr (relCond l) (relCond r)
relCond (SqlAnd l r)    = RAnd (relCond l) (relCond r)

-- | optimizes the selection queries.
optRSel :: RAlgebra -> RAlgebra
-- σ c₁ (σ c₂ q) ≡ σ (c₁ ∧ c₂) q
optRSel (RSel c1 (Rename Nothing (RSel c2 rq))) 
  = RSel (SqlAnd c1 c2) (renameMap optRSel rq)
-- σ c₁ (π l (σ c₂ q)) ≡ π l (σ (c₁ ∧ c₂) q)
-- discuss this with Eric?
-- optSel q@(Sel c1 (Rename Nothing (Proj as (Rename n (Sel c2 rq)))))
--   | noAttRename as = Proj as (Rename n (Sel (VsqlAnd c1 c2) (renameMap optSel rq)))
--   | otherwise      = q
--     where
--       noAttRename :: OptAttributes -> Bool
--       noAttRename as = and $ fmap (isNothing . name . getObj) as
-- σ c (q₁ × q₂) ≡ q₁ ⋈\_c q₂
optRSel q@(RSel c (Rename Nothing (RProd rq1 rq2)))
  | notInCond c = RJoin (renameMap optRSel rq1) (renameMap optRSel rq2) (relCond c)
  | otherwise   = q 
-- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_(c₁ ∧ c₂) q₂
optRSel q@(RSel c1 (Rename Nothing (RJoin rq1 rq2 c2)))
  | notInCond c1 = RJoin rq1 rq2 (RAnd (relCond c1) c2)
  | otherwise    = q
optRSel (RSel c rq)       = RSel c (renameMap optRSel rq)
optRSel (RSetOp o q1 q2)  = RSetOp o (optRSel q1) (optRSel q2)
optRSel (RProj as rq)     = RProj as (renameMap optRSel rq)
optRSel (RJoin rq1 rq2 c) = RJoin (renameMap optRSel rq1) (renameMap optRSel rq2) c 
optRSel (RProd rq1 rq2)   = RProd (renameMap optRSel rq1) (renameMap optRSel rq2)
optRSel q                 = q

-- | selection distributive properties.
selRDistr :: RAlgebra -> RSchema -> RAlgebra
selRDistr q@(RSel (SqlAnd c1 c2) (Rename Nothing (RJoin rq1 rq2 c))) s 
  -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₁ q₁) ⋈\_c (σ c₂ q₂)
  | check c1 t1 && check c2 t2 
    = RJoin (Rename Nothing (RSel c1 (renameMap selRDistr' rq1))) 
            (Rename Nothing (RSel c2 (renameMap selRDistr' rq2)))
            c
  -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₂ q₁) ⋈\_c (σ c₁ q₂)
  | check c2 t1 && check c1 t2 
    = RJoin (Rename Nothing (RSel c2 (renameMap selRDistr' rq1))) 
            (Rename Nothing (RSel c1 (renameMap selRDistr' rq2))) 
            c
  | otherwise = q 
    where 
      selRDistr' = flip selRDistr s 
      check cond env = (not (notInCond cond) && inAttInEnv cond env)
                    || (notInCond cond && condAttsInEnv (relCond cond) env)
      t1 = fromJust $ typeOfRQuery (thing rq1) s 
      t2 = fromJust $ typeOfRQuery (thing rq2) s 
selRDistr q@(RSel c1 (Rename Nothing (RJoin rq1 rq2 c2))) s
  -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ (σ c₁ q₁) ⋈\_c₂ q₂
  | check c1 t1
    = RJoin (Rename Nothing (RSel c1 (renameMap (flip selRDistr s) rq1))) 
           (renameMap (flip selRDistr s) rq2) 
           c2
  -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_c₂ (σ c₁ q₂)
  | check c1 t2
    = RJoin (renameMap (flip selRDistr s) rq1) 
           (Rename Nothing (RSel c1 (renameMap (flip selRDistr s) rq2))) 
           c2
  | otherwise = q 
    where
      check cond env = (not (notInCond cond) && inAttInEnv cond env)
                    || (notInCond cond && condAttsInEnv (relCond cond) env)
      t1 = fromJust $ typeOfRQuery (thing rq1) s 
      t2 = fromJust $ typeOfRQuery (thing rq2) s 
selRDistr (RSel c rq)       s 
  = RSel c (renameMap (flip selRDistr s) rq)
selRDistr (RSetOp o q1 q2)  s 
  = RSetOp o (selRDistr q1 s ) (selRDistr q2 s)
selRDistr (RProj as rq)     s 
  = RProj as (renameMap (flip selRDistr s) rq)
selRDistr (RJoin rq1 rq2 c) s
  = RJoin (renameMap (flip selRDistr s) rq1)
         (renameMap (flip selRDistr s) rq2)
         c 
selRDistr (RProd rq1 rq2)   s 
  = RProd (renameMap (flip selRDistr s) rq1)
         (renameMap (flip selRDistr s) rq2)
selRDistr q _ = q 

-- | gets a condition of the "IN" format and determines if
--   its attribute exists in a type env.
inAttInEnv :: SqlCond RAlgebra -> RTypeEnv -> Bool
inAttInEnv (SqlIn a _) t = attInEnv a t 
inAttInEnv _ _ = error "Can only accept conditions of the IN format!!"

-- | checks if an attribute exists in a type env or not.
attInEnv :: Attr -> RTypeEnv -> Bool
attInEnv a t = maybe False (\ _ -> True) (SM.lookup (attribute a) t)

-- | takes a relational condition and determines if it's 
--   consistent with a type env.
condAttsInEnv :: RCondition -> RTypeEnv -> Bool
condAttsInEnv (RLit _)        _ = True
condAttsInEnv (RComp _ a1 a2) t = case (a1, a2) of 
  (Val _, Att a)  -> attInEnv a t 
  (Att a, Val _)  -> attInEnv a t 
  (Att a, Att a') -> attInEnv a t && attInEnv a' t 
  _               -> True 
condAttsInEnv (RNot c)        t = condAttsInEnv c t 
condAttsInEnv (ROr c1 c2)     t = condAttsInEnv c1 t && condAttsInEnv c2 t 
condAttsInEnv (RAnd c1 c2)    t = condAttsInEnv c1 t && condAttsInEnv c2 t 

-- | projection distributive properties.
prjRDistr :: RAlgebra -> RSchema -> RAlgebra
-- π (l₁, l₂) (q₁ ⋈\_c q₂) ≡ (π l₁ q₁) ⋈\_c (π l₂ q₂)
prjRDistr (RProj as (Rename Nothing (RJoin rq1 rq2 c))) s 
  = RJoin (Rename Nothing (RProj as1 (renameMap prjDistr' rq1)))
          (Rename Nothing (RProj as2 (renameMap prjDistr' rq2)))
          c
    where
      t1  = fromJust $ typeOfRQuery (thing rq1) s 
      pas = partitionAtts as (name rq1) t1
      as1 = fst pas 
      as2 = snd pas 
      prjDistr' = flip prjRDistr s 
prjRDistr (RProj as rq)     s 
  = RProj as (renameMap (flip prjRDistr s) rq)
prjRDistr (RSetOp o q1 q2)  s 
  = RSetOp o (prjRDistr q1 s) (prjRDistr q2 s)
prjRDistr (RSel c rq)       s 
  = RSel c (renameMap (flip prjRDistr s) rq)
prjRDistr (RJoin rq1 rq2 c) s 
  = RJoin (renameMap (flip prjRDistr s) rq1)
          (renameMap (flip prjRDistr s) rq2)
          c
prjRDistr (RProd rq1 rq2)  s
  = RProd (renameMap (flip prjRDistr s) rq1)
          (renameMap (flip prjRDistr s) rq2)
prjRDistr q _ = q 
-- π (l₁, l₂) ((π (l₁, l₃) q₁) ⋈\_c (π (l₂, l₄) q₂)) ≡ π (l₁, l₂) (q₁ ⋈\_c q₂)
-- discuss with Eric. don't think we need this since we can regenerate
-- it with prjDistr and pushOutPrj

-- | partitions a list of attributes based on a given type env.
partitionAtts :: Attributes -> Alias -> RTypeEnv -> (Attributes, Attributes)
partitionAtts as n t = partition divideAtt as 
  where
    divideAtt :: Rename Attr -> Bool
    divideAtt a = maybe False 
                        (\inf -> maybe True
                           (`elem` fmap rAttrQual inf) 
                           ((qualifier . thing) a))
                        (SM.lookup ((attribute . thing) a) t')
    t' = updateType n t 








