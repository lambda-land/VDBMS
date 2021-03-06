-- | Variation minimization of variational relational queries.
-- ASSUMPTION: queries have been type checked before being
--             optimized!! 
module VDBMS.QueryLang.RelAlg.Variational.Minimization (

       -- appMin
       -- , runAppMin
       -- , minPushedSch
       -- , confMinPushedQ
       -- , optMinPushedQ
       -- , 
       chcSimpleReduceRec
       
) where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import VDBMS.TypeSystem.Variational.TypeSystem
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Variational.Opt (Opt(..), mapFst, getObj, getFexp, applyFuncFexp, mkOpt)
import VDBMS.Features.SAT
import VDBMS.QueryGen.VRA.PushSchToQ
-- for test
import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.Features.Config (Config)
import VDBMS.Variational.Variational (Variational(..))
-- 


import qualified Data.Map.Strict as SM (lookup)
import Data.Maybe (catMaybes, fromJust)
import Data.List (partition)

import Data.Generics.Uniplate.Operations (transform)

-- | optionalizes a query after minpush.
-- optMinPushedQ :: Schema -> Algebra -> [Opt RAlgebra]
-- optMinPushedQ s q = optionalize_ (minPushedSch s q)

-- -- | configures a query after minpush.
-- confMinPushedQ :: Config Bool -> Schema -> Algebra -> RAlgebra
-- confMinPushedQ c s q = configure c (minPushedSch s q)

-- -- | min q after push sch to it.
-- minPushedSch :: Schema -> Algebra -> Algebra
-- minPushedSch s q = runAppMin s (pushSchToQ s q)

-- -- | appMin initiated with feature model of the schema.
-- runAppMin :: Schema -> Algebra -> Algebra
-- runAppMin s q = appMin q (featureModel s) s

-- -- | Applies the minimization rules until the query doesn't change.
-- appMin :: Algebra -> VariationalContext -> Schema -> Algebra
-- appMin q ctx s
--   | minVar q ctx s == q = q 
--   | otherwise           = appMin (minVar q ctx s) ctx s

-- -- | Variation minimization rules.
-- -- Note: not sure which side is more optimized. We can determine that by
-- --       running some experiments. It also probably depends on the 
-- --       approach we take.
-- minVar :: Algebra -> VariationalContext -> Schema -> Algebra 
-- minVar q _ _ = chcSimpleReduceRec q
  -- prjDistr (selDistrRec ((chcRelRec . optSelRec . pushOutProjRec . chcDistrRec . chcSimpleReduceRec) q) ctx s) ctx s

-- | Applies a feature expression to all attributes in an opt attrs.
-- denoted as: lᶠ
appFexpOptAtts :: F.FeatureExpr -> OptAttributes -> OptAttributes
appFexpOptAtts f = mapFst (F.And f) 

-- | recursive application of chcsimple.
chcSimpleReduceRec :: Algebra -> Algebra
chcSimpleReduceRec = transform chcSimpleReduce

-- | simple reductions of chc.
chcSimpleReduce :: Algebra -> Algebra
chcSimpleReduce (AChc (F.Lit True) q1 q2) = q1
chcSimpleReduce (AChc (F.Lit False) q1 q2) = q2
chcSimpleReduce (AChc f q1 q2)
  | tautology f = q1
  | unsatisfiable f = q2
chcSimpleReduce q = q

-- | recursive application of chcdistr rules.
chcDistrRec :: Algebra -> Algebra
chcDistrRec = transform chcDistr

-- | Choice distributive laws.
chcDistr :: Algebra -> Algebra
-- f<π l₁ q₁, π l₂ q₂> ≡ π (f<l₁, l₂>) f<q₁, q₂>
-- f<π l₁ q₁, π l₂ q₂> ≡ π ((l₁ᶠ), (l₂ \^¬f )) f<q₁, q₂>
chcDistr (AChc f (Proj l1 q1) (Proj l2 q2))
  = Proj (appFexpOptAtts f l1 ++ appFexpOptAtts (F.Not f) l2)
         (AChc f q1 q2)
-- f<σ c₁ q₁, σ c₂ q₂> ≡ σ f<c₁, c₂> f<q₁, q₂>
chcDistr (AChc f (Sel c1 q1) (Sel c2 q2))
  = Sel (VsqlCChc f c1 c2) 
        (AChc f q1 q2)
-- f<q₁ × q₂, q₃ × q₄> ≡ f<q₁, q₃> × f<q₂, q₄>
chcDistr (AChc f (Prod q1 q2) (Prod q3 q4)) 
  = Prod (AChc f q1 q3) (AChc f q2 q4)
-- f<q₁ ⋈\_c₁ q₂, q₃ ⋈\_c₂ q₄> ≡ f<q₁, q₃> ⋈\_(f<c₁, c₂>) f<q₂, q₄>
chcDistr (AChc f (Join q1 q2 c1) (Join q3 q4 c2))
  = Join (AChc f q1 q3) (AChc f q2 q4) (CChc f c1 c2)
-- f<q₁ ∪ q₂, q₃ ∪ q₄> ≡ f<q₁, q₃> ∪ f<q₂, q₄>
chcDistr (AChc f (SetOp Union q1 q2) (SetOp Union q3 q4))
  = SetOp Union (AChc f q1 q3) (AChc f q2 q4)
-- f<q₁ ∩ q₂, q₃ ∩ q₄> ≡ f<q₁, q₃> ∩ f<q₂, q₄>
chcDistr (AChc f (SetOp Diff q1 q2) (SetOp Diff q3 q4))
  = SetOp Diff (AChc f q1 q3) (AChc f q2 q4)
-- chcDistr (RenameAlg n q) = RenameAlg n (chcDistr q)
chcDistr q = q

-- | recursive application of push out prj.
pushOutProjRec :: Algebra -> Algebra
pushOutProjRec = transform pushOutProj

-- | Pushes out projection as far as possible.
-- Note that you don't necessarily want to push out all projs.
-- Eg: proj l1 R * proj l2 S = proj (l1 + l2) (R * S)
--     but the rhs isn't more efficient than the lhs! keep in 
--     min that the same goes for joins.
-- There are also cases that you CANNOT push out projs:
-- Eg: proj l1 q1 `union` proj l1 q2 <> proj l1 (q1 `union` q2)
pushOutProj :: Algebra -> Algebra
-- σ c (π l q) ≡ π l (σ c q)
pushOutProj (Sel c (Proj as q)) = Proj as (Sel c q)
-- π l₁ (π l₂ q) ≡ π l₁ q
-- if the attribute in as1 is previously
-- projected in as2 you need to conjunct their fexps!
pushOutProj (Proj as1 (Proj as2 q)) 
  = Proj (updateAtts as1 as2) q
    where
      updateAtts :: OptAttributes -> OptAttributes -> OptAttributes
      updateAtts orgs subs = [ compAtts a subs | a <- orgs]
      compAtts :: OptAttribute -> OptAttributes -> OptAttribute
      compAtts a as 
        | null attList = a 
        | otherwise = head attList 
          where attList = catMaybes [ compAtt a att | att <- as]
      compAtt :: OptAttribute -> OptAttribute -> Maybe OptAttribute
      compAtt a1 a2 
        | attrOfOptAttr a1 == attrOfOptAttr a2 
            = Just $ applyFuncFexp (F.shrinkFExp . (F.And (getFexp a1))) a2
                           -- (Rename (attrAlias a1) ((thing . getObj) a2))
        -- | attrAlias a2 /= Nothing 
        --   && attrName a1 == (fromJust (attrAlias a2))
        --     = Just $ applyFuncFexp (F.And (getFexp a1)) a2
        | otherwise = Nothing
-- TODO: possible refactory: 
-- π l f⟨q1, q2⟩ ≡ f ⟨π l' q1, π l'' q2⟩
-- where l' and l'' are subsets of l that are included in q1 and q2's types respectively.
pushOutProj q = q 

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

-- | recursive application of optsel.
optSelRec :: Algebra -> Algebra
optSelRec = transform optSel

-- | optimizes the selection queries.
optSel :: Algebra -> Algebra
-- σ c₁ (σ c₂ q) ≡ σ (c₁ ∧ c₂) q
optSel (Sel c1 (Sel c2 q))
  = Sel (VsqlAnd c1 c2) q
-- σ c₁ (π l (σ c₂ q)) ≡ π l (σ (c₁ ∧ c₂) q)
optSel (Sel c1 (Proj as (Sel c2 q)))
  = Proj as (Sel (VsqlAnd c1 c2) q)
-- σ c (q₁ × q₂) ≡ q₁ ⋈\_c q₂
optSel q@(Sel c (Prod q1 q2))
  | notInCond c = Join q1 q2 (relCond c)
  | otherwise   = q 
-- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_(c₁ ∧ c₂) q₂
optSel q@(Sel c1 (Join q1 q2 c2))
  | notInCond c1 = Join q1 q2 (And (relCond c1) c2)
  | otherwise    = q
optSel q                = q

-- | recursive appication of sel distr.
selDistrRec :: Algebra -> VariationalContext -> Schema -> Algebra
selDistrRec q ctx s = transform (flip (flip selDistr ctx) s) q

-- | selection distributive properties.
selDistr :: Algebra -> VariationalContext -> Schema -> Algebra
selDistr q@(Sel (VsqlAnd c1 c2) (Join q1 q2 c)) ctx s 
  -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₁ q₁) ⋈\_c (σ c₂ q₂)
  | check c1 t1 && check c2 t2 
    = Join (Sel c1 q1) (Sel c2 q2) c
  -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₂ q₁) ⋈\_c (σ c₁ q₂)
  | check c2 t1 && check c1 t2 
    = Join (Sel c2 q1) (Sel c1 q2) c
  | otherwise = q
    where 
      -- selDistr' q' = selDistr q' ctx s 
      check cond env = (not (notInCond cond) && inAttInEnv cond env)
                    || (notInCond cond && condAttsInEnv (relCond cond) env)
      t1 = fromJust $ typeOfQuery q1 ctx s 
      t2 = fromJust $ typeOfQuery q2 ctx s 
selDistr q@(Sel c1 (Join q1 q2 c2)) ctx s
  -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ (σ c₁ q₁) ⋈\_c₂ q₂
  | check c1 t1
    = Join (Sel c1 q1) q2 c2
  -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_c₂ (σ c₁ q₂)
  | check c1 t2
    = Join q1 (Sel c1 q2) c2
  | otherwise = q 
    where
      -- selDistr' q' = selDistr q' ctx s 
      check cond env = (not (notInCond cond) && inAttInEnv cond env)
                    || (notInCond cond && condAttsInEnv (relCond cond) env)
      t1 = fromJust $ typeOfQuery q1 ctx s 
      t2 = fromJust $ typeOfQuery q2 ctx s 
selDistr q _ _ = q 

-- | gets a condition of the "IN" format and determines if
--   its attribute exists in a type env.
inAttInEnv :: VsqlCond -> TypeEnv -> Bool
inAttInEnv (VsqlIn a _) t = attInEnv a t 
inAttInEnv _ _ = error "Can only accept conditions of the IN format!!"

-- | checks if an attribute exists in a type env or not.
attInEnv :: Attr -> TypeEnv -> Bool
attInEnv a t = maybe False (\ _ -> True) (SM.lookup (attribute a) (getObj t))

-- | takes a relational condition and determines if it's 
--   consistent with a type env.
condAttsInEnv :: Condition -> TypeEnv -> Bool
condAttsInEnv (Lit _)        _ = True
condAttsInEnv (Comp _ a1 a2) t = case (a1, a2) of 
  (Val _, Att a)  -> attInEnv a t 
  (Att a, Val _)  -> attInEnv a t 
  (Att a, Att a') -> attInEnv a t && attInEnv a' t 
  _               -> True 
condAttsInEnv (Not c)        t = condAttsInEnv c t 
condAttsInEnv (Or c1 c2)     t = condAttsInEnv c1 t && condAttsInEnv c2 t 
condAttsInEnv (And c1 c2)    t = condAttsInEnv c1 t && condAttsInEnv c2 t 
condAttsInEnv (CChc _ c1 c2) t = condAttsInEnv c1 t && condAttsInEnv c2 t

-- -- | recursive application of prj dist.
-- prjDistrRec :: Algebra -> VariationalContext -> Schema -> Algebra
-- prjDistrRec q ctx s = transform (flip (flip prjDistr ctx) s) q

-- -- | projection distributive properties.
-- prjDistr :: Algebra -> VariationalContext -> Schema -> Algebra
-- -- π (l₁, l₂) (q₁ ⋈\_c q₂) ≡ (π l₁ q₁) ⋈\_c (π l₂ q₂)
-- prjDistr (Proj as (Join q1 q2 c)) ctx s = undefined
--   -- = Join (Rename Nothing (Proj as1 (renameMap prjDistr' rq1)))
--   --        (Rename Nothing (Proj as2 (renameMap prjDistr' rq2)))
--   --        c
--   --   where
--   --     t1 = fromJust $ typeOfQuery (thing rq1) ctx s 
--   --     pas = partitionAtts as (name rq1) t1
--   --     as1 = fst pas 
--   --     as2 = snd pas 
--   --     prjDistr' q = prjDistr q ctx s 
-- prjDistr q _ _ = q 
-- -- π (l₁, l₂) ((π (l₁, l₃) q₁) ⋈\_c (π (l₂, l₄) q₂)) ≡ π (l₁, l₂) (q₁ ⋈\_c q₂)
-- -- discuss with Eric. don't think we need this since we can regenerate
-- -- it with prjDistr and pushOutPrj

-- -- | partitions a list of attributes based on a given type env.
-- partitionAtts :: OptAttributes -> Alias -> TypeEnv -> (OptAttributes, OptAttributes)
-- partitionAtts as n t = undefined
--   -- partition divideAtt as 
--   -- where
--   --   divideAtt :: OptAttribute -> Bool
--   --   divideAtt a = maybe False 
--   --                       (\inf -> maybe True
--   --                          (`elem` fmap attrQual inf) 
--   --                          ((qualifier . thing . getObj) a))
--   --                       (SM.lookup (attrOfOptAttr a) (getObj t'))
--   --   t' = updateType n t 

-- | choices rules.

-- | recursive application of chc.
chcRelRec :: Algebra -> Algebra
chcRelRec = transform chcRel

-- | relational alg and choices combined rules.
-- Note: the last three combination rules in my masters thesis 
--       can be generated from the combination of other rules.
-- Discuss the note with Eric.
chcRel :: Algebra -> Algebra
-- f<σ (c₁ ∧ c₂) q₁, σ (c₁ ∧ c₃) q₂> ≡ σ (c₁ ∧ f<c₂, c₃>) f<q₁, q₂>
chcRel q@(AChc f (Sel (VsqlAnd c1 c2) q1) 
                 (Sel (VsqlAnd c3 c4) q2))
  | vsqlCondEq c1 c3 
    = Sel (VsqlAnd c1 (VsqlCChc f c2 c4)) (AChc f q1 q2)
  | vsqlCondEq c1 c4 
    = Sel (VsqlAnd c1 (VsqlCChc f c2 c3)) (AChc f q1 q2)
  | vsqlCondEq c2 c3 
    = Sel (VsqlAnd c2 (VsqlCChc f c1 c4)) (AChc f q1 q2)
  | vsqlCondEq c2 c4 
    = Sel (VsqlAnd c2 (VsqlCChc f c1 c3)) (AChc f q1 q2)
  | otherwise = q
chcRel q@(AChc f (Sel (VsqlCond (And c1 c2)) q1)
                 (Sel (VsqlAnd c3 c4) q2))
  | vsqlCondEq (VsqlCond c1) c3 
    = Sel (VsqlAnd (VsqlCond c1) (VsqlCChc f (VsqlCond c2) c4)) 
          (AChc f q1 q2)
  | vsqlCondEq (VsqlCond c1) c4 
    = Sel (VsqlAnd (VsqlCond c1) (VsqlCChc f (VsqlCond c2) c3)) 
          (AChc f q1 q2)
  | vsqlCondEq (VsqlCond c2) c3 
    = Sel (VsqlAnd (VsqlCond c2) (VsqlCChc f (VsqlCond c1) c4)) 
          (AChc f q1 q2)
  | vsqlCondEq (VsqlCond c2) c4 
    = Sel (VsqlAnd (VsqlCond c2) (VsqlCChc f (VsqlCond c1) c3)) 
          (AChc f q1 q2)
  | otherwise = q
chcRel q@(AChc f (Sel (VsqlAnd c1 c2) q1) 
                 (Sel (VsqlCond (And c3 c4)) q2))
  | vsqlCondEq c1 (VsqlCond c3) 
    = Sel (VsqlAnd c1 (VsqlCChc f c2 (VsqlCond c4))) 
          (AChc f q1 q2)
  | vsqlCondEq c1 (VsqlCond c4) 
    = Sel (VsqlAnd c1 (VsqlCChc f c2 (VsqlCond c3))) 
          (AChc f q1 q2)
  | vsqlCondEq c2 (VsqlCond c3) 
    = Sel (VsqlAnd c2 (VsqlCChc f c1 (VsqlCond c4))) 
          (AChc f q1 q2)
  | vsqlCondEq c2 (VsqlCond c4) 
    = Sel (VsqlAnd c2 (VsqlCChc f c1 (VsqlCond c3))) 
          (AChc f q1 q2)
  | otherwise = q
chcRel q@(AChc f (Sel (VsqlCond (And c1 c2)) q1)
                 (Sel (VsqlCond (And c3 c4)) q2))
  | conditionEq c1 c3 
    = Sel (VsqlAnd (VsqlCond c1) (VsqlCChc f (VsqlCond c2) (VsqlCond c4))) 
          (AChc f q1 q2)
  | conditionEq c1 c4 
    = Sel (VsqlAnd (VsqlCond c1) (VsqlCChc f (VsqlCond c2) (VsqlCond c3))) 
          (AChc f q1 q2)
  | conditionEq c2 c3 
    = Sel (VsqlAnd (VsqlCond c2) (VsqlCChc f (VsqlCond c1) (VsqlCond c4))) 
          (AChc f q1 q2)
  | conditionEq c2 c4 
    = Sel (VsqlAnd (VsqlCond c2) (VsqlCChc f (VsqlCond c1) (VsqlCond c3)))
          (AChc f q1 q2)
  | otherwise = q
-- σ c₁ (f<σ c₂ q₁, σ c₃ q₂>) ≡ σ (c₁ ∧ f<c₂, c₃>) f<q₁, q₂>
chcRel (Sel c1 (AChc f (Sel c2  q1)
                       (Sel c3 q2)))
  = Sel (VsqlAnd c1 (VsqlCChc f c2 c3)) (AChc f q1 q2)
-- f<q₁ ⋈\_(c₁ ∧ c₂) q₂, q₃ ⋈\_(c₁ ∧ c₃) q₄> ≡ σ (f<c₂, c₃>) (f<q₁, q₃> ⋈\_c₁ f<q₂, q₄>)
chcRel q@(AChc f (Join q1 q2 (And c1 c2)) 
                 (Join q3 q4 (And c3 c4)))
  | conditionEq c1 c3 
    = Sel (VsqlCChc f (VsqlCond c2) (VsqlCond c4)) 
          (Join (AChc f q1 q3)
                (AChc f q2 q4) c1)
  | conditionEq c1 c4 
    = Sel (VsqlCChc f (VsqlCond c2) (VsqlCond c3))
          (Join (AChc f q1 q3)
                (AChc f q2 q4) c1)
  | conditionEq c2 c3 
    = Sel (VsqlCChc f (VsqlCond c1) (VsqlCond c4))
          (Join (AChc f q1 q3)
                (AChc f q2 q4) c2)
  | conditionEq c2 c4 
    = Sel (VsqlCChc f (VsqlCond c1) (VsqlCond c3))
          (Join (AChc f q1 q3)
                (AChc f q2 q4) c2)
  | otherwise = q
-- chcRel (RenameAlg n q) = RenameAlg n (chcRel q)
chcRel q = q






