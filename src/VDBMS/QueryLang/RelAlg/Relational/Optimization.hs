-- | relational alg optimization rules.
module VDBMS.QueryLang.RelAlg.Relational.Optimization where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
-- import VDBMS.TypeSystem.Variational.TypeSystem
import VDBMS.VDB.Schema.Relational.Types
-- -- import VDBMS.Features.Config
-- -- import VDBMS.QueryLang.ConfigQuery
-- import VDBMS.Variational.Opt (mapFst, getObj, getFexp, applyFuncFexp, mkOpt)
-- -- import VDBMS.Variational.Variational

-- import qualified Data.Map as M 
-- import qualified Data.Map.Strict as SM (lookup)
import Data.Maybe (catMaybes, fromJust)
-- import Data.List (partition)

-- | Applies the minimization rules until the query doesn't change.
appOpt :: RAlgebra -> RSchema -> RAlgebra
appOpt q s
  | opts q s == q = q 
  | otherwise     = appOpt (opts q s) s

-- | Relational optimization rules.
opts :: RAlgebra -> RSchema -> RAlgebra 
opts q s = 
  prjDistr (selDistr ((optSel . pushOutProj) q) s) s

-- | Pushes out projection as far as possible.
-- Note that you don't necessarily want to push out all projs.
-- Eg: proj l1 R * proj l2 S = proj (l1 + l2) (R * S)
--     but the rhs isn't more efficient than the lhs! keep in 
--     min that the same goes for joins.
-- There are also cases that you CANNOT push out projs:
-- Eg: proj l1 q1 `union` proj l1 q2 <> proj l1 (q1 `union` q2)
pushOutProj :: RAlgebra -> RAlgebra
-- pushOutProj = undefined
-- σ c (π l q) ≡ π l (σ c q)
pushOutProj (RSel c (Rename Nothing (RProj as rq)))
  = RProj as (Rename Nothing (RSel c (renameMap pushOutProj rq)))
-- π l₁ (π l₂ q) ≡ π l₁ q
-- checks if renaming happened in l₂ and update 
-- l₁ appropriately! 
pushOutProj (RProj as1 (Rename Nothing (RProj as2 rq)))
  = RProj (updateAtts as1 as2) (renameMap pushOutProj rq)
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
pushOutProj (RSetOp o q1 q2)
  = RSetOp o (pushOutProj q1) (pushOutProj q2)
pushOutProj (RJoin rq1 rq2 c)
  = RJoin (renameMap pushOutProj rq1) (renameMap pushOutProj rq2) c
pushOutProj (RProd rq1 rq2) 
  = RProd (renameMap pushOutProj rq1) (renameMap pushOutProj rq2)
pushOutProj q = q 

-- | checks if a sql condition is of the form "attr in query" condition.
-- notInCond :: VsqlCond -> Bool 
-- notInCond (VsqlIn _ _)     = True
-- notInCond (VsqlCond _)     = False
-- notInCond (VsqlNot c)      = notInCond c
-- notInCond (VsqlOr l r)     = notInCond l && notInCond r
-- notInCond (VsqlAnd l r)    = notInCond l && notInCond r 
-- notInCond (VsqlCChc _ l r) = notInCond l && notInCond r 

-- | knowing that the sql condition is not of the form "attr in query"
--   converts the sql condition to a relational condition.
-- relCond :: VsqlCond -> Condition
-- relCond (VsqlCond c)     = c 
-- relCond (VsqlIn _ _)     = error $ "didn't expect to get a condition of the form attr in query!! QUERY VAR MIN!!"
-- relCond (VsqlNot c)      = Not (relCond c)
-- relCond (VsqlOr l r)     = Or (relCond l) (relCond r)
-- relCond (VsqlAnd l r)    = And (relCond l) (relCond r)
-- relCond (VsqlCChc f l r) = CChc f (relCond l) (relCond r)

-- | optimizes the selection queries.
optSel :: RAlgebra -> RAlgebra
optSel = undefined
-- -- σ c₁ (σ c₂ q) ≡ σ (c₁ ∧ c₂) q
-- optSel (Sel c1 (Rename Nothing (Sel c2 rq))) 
--   = Sel (VsqlAnd c1 c2) (renameMap optSel rq)
-- -- σ c₁ (π l (σ c₂ q)) ≡ π l (σ (c₁ ∧ c₂) q)
-- -- discuss this with Eric?
-- -- optSel q@(Sel c1 (Rename Nothing (Proj as (Rename n (Sel c2 rq)))))
-- --   | noAttRename as = Proj as (Rename n (Sel (VsqlAnd c1 c2) (renameMap optSel rq)))
-- --   | otherwise      = q
-- --     where
-- --       noAttRename :: OptAttributes -> Bool
-- --       noAttRename as = and $ fmap (isNothing . name . getObj) as
-- -- σ c (q₁ × q₂) ≡ q₁ ⋈\_c q₂
-- optSel q@(Sel c (Rename Nothing (Prod rq1 rq2)))
--   | notInCond c = Join (renameMap optSel rq1) (renameMap optSel rq2) (relCond c)
--   | otherwise   = q 
-- -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_(c₁ ∧ c₂) q₂
-- optSel q@(Sel c1 (Rename Nothing (Join rq1 rq2 c2)))
--   | notInCond c1 = Join rq1 rq2 (And (relCond c1) c2)
--   | otherwise    = q
-- optSel (Sel c rq)       = Sel c (renameMap optSel rq)
-- optSel (SetOp o q1 q2)  = SetOp o (optSel q1) (optSel q2)
-- optSel (Proj as rq)     = Proj as (renameMap optSel rq)
-- optSel (AChc f q1 q2)   = AChc f (optSel q1) (optSel q2)
-- optSel (Join rq1 rq2 c) = Join (renameMap optSel rq1) (renameMap optSel rq2) c 
-- optSel (Prod rq1 rq2)   = Prod (renameMap optSel rq1) (renameMap optSel rq2)
-- optSel q                = q

-- | selection distributive properties.
selDistr :: RAlgebra -> RSchema -> RAlgebra
selDistr = undefined
-- selDistr q@(Sel c1 (Rename Nothing (Join rq1 rq2 c2))) ctx s
--   -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ (σ c₁ q₁) ⋈\_c₂ q₂
--   | check c1 t1
--     = Join (Rename Nothing (Sel c1 (renameMap selDistr' rq1))) 
--            (renameMap selDistr' rq2) 
--            c2
--   -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_c₂ (σ c₁ q₂)
--   | check c1 t2
--     = Join (renameMap selDistr' rq1) 
--            (Rename Nothing (Sel c1 (renameMap selDistr' rq2))) 
--            c2
--   | otherwise = q 
--     where
--       selDistr' q' = selDistr q' ctx s 
--       check cond env = (not (notInCond cond) && inAttInEnv cond env)
--                     || (notInCond cond && condAttsInEnv (relCond cond) env)
--       t1 = fromJust $ typeOfQuery (thing rq1) ctx s 
--       t2 = fromJust $ typeOfQuery (thing rq2) ctx s 
-- selDistr q@(Sel (VsqlAnd c1 c2) (Rename Nothing (Join rq1 rq2 c))) ctx s 
--   -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₁ q₁) ⋈\_c (σ c₂ q₂)
--   | check c1 t1 && check c2 t2 
--     = Join (Rename Nothing (Sel c1 (renameMap selDistr' rq1))) 
--            (Rename Nothing (Sel c2 (renameMap selDistr' rq2)))
--            c
--   -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₂ q₁) ⋈\_c (σ c₁ q₂)
--   | check c2 t1 && check c1 t2 
--     = Join (Rename Nothing (Sel c2 (renameMap selDistr' rq1))) 
--            (Rename Nothing (Sel c1 (renameMap selDistr' rq2))) 
--            c
--     where 
--       selDistr' q' = selDistr q' ctx s 
--       check cond env = (not (notInCond cond) && inAttInEnv cond env)
--                     || (notInCond cond && condAttsInEnv (relCond cond) env)
--       t1 = fromJust $ typeOfQuery (thing rq1) ctx s 
--       t2 = fromJust $ typeOfQuery (thing rq2) ctx s 
-- selDistr (Sel c rq)       ctx s 
--   = Sel c (renameMap (flip (flip selDistr ctx) s) rq)
-- selDistr (SetOp o q1 q2)  ctx s 
--   = SetOp o (selDistr q1 ctx s ) (selDistr q2 ctx s)
-- selDistr (Proj as rq)     ctx s 
--   = Proj as (renameMap (flip (flip selDistr ctx) s) rq)
-- selDistr (AChc f q1 q2)   ctx s 
--   = AChc f (selDistr q1 ctx s) (selDistr q2 ctx s)
-- selDistr (Join rq1 rq2 c) ctx s
--   = Join (renameMap (flip (flip selDistr ctx) s) rq1)
--          (renameMap (flip (flip selDistr ctx) s) rq2)
--          c 
-- selDistr (Prod rq1 rq2)   ctx s 
--   = Prod (renameMap (flip (flip selDistr ctx) s) rq1)
--          (renameMap (flip (flip selDistr ctx) s) rq2)
-- selDistr q ctx s = q 

-- | gets a condition of the "IN" format and determines if
--   its attribute exists in a type env.
-- inAttInEnv :: VsqlCond -> TypeEnv -> Bool
-- inAttInEnv (VsqlIn a q) t = attInEnv a t 
-- inAttInEnv _ _ = error "Can only accept conditions of the IN format!!"

-- | checks if an attribute exists in a type env or not.
-- attInEnv :: Attr -> TypeEnv -> Bool
-- attInEnv a t = maybe False (\ _ -> True) (SM.lookup (attribute a) (getObj t))

-- | takes a relational condition and determines if it's 
--   consistent with a type env.
-- condAttsInEnv :: Condition -> TypeEnv -> Bool
-- condAttsInEnv (Lit b)        t = True
-- condAttsInEnv (Comp o a1 a2) t = case (a1, a2) of 
--   (Val v, Att a)  -> attInEnv a t 
--   (Att a, Val v)  -> attInEnv a t 
--   (Att a, Att a') -> attInEnv a t && attInEnv a' t 
--   _               -> True 
-- condAttsInEnv (Not c)        t = condAttsInEnv c t 
-- condAttsInEnv (Or c1 c2)     t = condAttsInEnv c1 t && condAttsInEnv c2 t 
-- condAttsInEnv (And c1 c2)    t = condAttsInEnv c1 t && condAttsInEnv c2 t 
-- condAttsInEnv (CChc f c1 c2) t = condAttsInEnv c1 t && condAttsInEnv c2 t

-- | projection distributive properties.
prjDistr :: RAlgebra -> RSchema -> RAlgebra
prjDistr = undefined
-- -- π (l₁, l₂) (q₁ ⋈\_c q₂) ≡ (π l₁ q₁) ⋈\_c (π l₂ q₂)
-- prjDistr (Proj as (Rename Nothing (Join rq1 rq2 c))) ctx s 
--   = Join (Rename Nothing (Proj as1 (renameMap prjDistr' rq1)))
--          (Rename Nothing (Proj as2 (renameMap prjDistr' rq2)))
--          c
--     where
--       t1 = fromJust $ typeOfQuery (thing rq1) ctx s 
--       pas = partitionAtts as (name rq1) t1
--       as1 = fst pas 
--       as2 = snd pas 
--       prjDistr' q = prjDistr q ctx s 
-- prjDistr (Proj as rq)     ctx s 
--   = Proj as (renameMap (flip (flip prjDistr ctx) s) rq)
-- prjDistr (SetOp o q1 q2)  ctx s 
--   = SetOp o (prjDistr q1 ctx s) (prjDistr q2 ctx s)
-- prjDistr (Sel c rq)       ctx s 
--   = Sel c (renameMap (flip (flip prjDistr ctx) s) rq)
-- prjDistr (AChc f q1 q2)   ctx s 
--   = AChc f (prjDistr q1 ctx s) (prjDistr q2 ctx s)
-- prjDistr (Join rq1 rq2 c) ctx s 
--   = Join (renameMap (flip (flip prjDistr ctx) s) rq1)
--          (renameMap (flip (flip prjDistr ctx) s) rq2)
--          c
-- prjDistr (Prod rq1 rq2)   ctx s
--   = Prod (renameMap (flip (flip prjDistr ctx) s) rq1)
--          (renameMap (flip (flip prjDistr ctx) s) rq2)
-- prjDistr q _ _ = q 
-- -- π (l₁, l₂) ((π (l₁, l₃) q₁) ⋈\_c (π (l₂, l₄) q₂)) ≡ π (l₁, l₂) (q₁ ⋈\_c q₂)
-- -- discuss with Eric. don't think we need this since we can regenerate
-- -- it with prjDistr and pushOutPrj

-- | partitions a list of attributes based on a given type env.
-- partitionAtts :: OptAttributes -> Alias -> TypeEnv -> (OptAttributes, OptAttributes)
-- partitionAtts as n t = partition divideAtt as 
--   where
--     divideAtt :: OptAttribute -> Bool
--     divideAtt a = maybe False 
--                         (\inf -> maybe True
--                            (`elem` fmap attrQual inf) 
--                            ((qualifier . thing . getObj) a))
--                         (SM.lookup (attrOfOptAttr a) (getObj t'))
--     t' = updateType n t 








