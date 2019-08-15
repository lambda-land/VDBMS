-- | Variation minimization of variational relational queries.
-- ASSUMPTION: queries have been type checked before being
--             optimized!! except for derived queries having
--             a new name!
module VDBMS.QueryLang.RelAlg.Variational.Minimization where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra 
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import VDBMS.TypeSystem.Variational.TypeSystem
import VDBMS.VDB.Schema.Variational.Schema
-- import VDBMS.Features.Config
-- import VDBMS.QueryLang.ConfigQuery
import VDBMS.Variational.Opt (mapFst, getObj, getFexp, applyFuncFexp, mkOpt)
-- import VDBMS.Variational.Variational

import Data.Maybe (isNothing, catMaybes, fromJust)

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
-- denoted as: lᶠ
appFexpOptAtts :: F.FeatureExpr -> OptAttributes -> OptAttributes
appFexpOptAtts f = mapFst (F.And f) 

-- | Choice distributive laws.
chcDistr :: Algebra -> Algebra
-- f<π l₁ q₁, π l₁ q₂> ≡ π ((l₁ᶠ), (l₂ \^¬f )) (q₁ × q₂)
chcDistr (AChc f (Proj l1 rq1) (Proj l2 rq2)) 
  = Proj (appFexpOptAtts f l1 ++ appFexpOptAtts (F.Not f) l2) 
         (Rename Nothing 
                (Prod (renameMap chcDistr rq1) 
                      (renameMap chcDistr rq2)))
-- f<σ c₁ q₁, σ c₂ q₂> ≡ σ f<c₁, c₂> f<q₁, q₂>
chcDistr (AChc f (Sel c1 rq1) (Sel c2 rq2))
  = Sel (VsqlCChc f c1 c2) 
        (Rename Nothing 
               (AChc f 
                    (thing (renameMap chcDistr rq1))
                    (thing (renameMap chcDistr rq2))))
-- f<q₁ × q₂, q₃ × q₄> ≡ f<q₁, q₃> × f<q₂, q₄>
chcDistr (AChc f (Prod rq1 rq2) (Prod rq3 rq4)) 
  = Prod (Rename Nothing 
                (AChc f 
                     (thing (renameMap chcDistr rq1))
                     (thing (renameMap chcDistr rq3)))) 
         (Rename Nothing 
                (AChc f 
                      (thing (renameMap chcDistr rq2))
                      (thing (renameMap chcDistr rq4))))
-- f<q₁ ⋈\_c₁ q₂, q₃ ⋈\_c₂ q₄> ≡ f<q₁, q₃> ⋈\_(f<c₁, c₂>) f<q₂, q₄>
chcDistr (AChc f (Join rq1 rq2 c1) (Join rq3 rq4 c2))
  = Join (Rename Nothing 
                (AChc f 
                     (thing (renameMap chcDistr rq1))
                     (thing (renameMap chcDistr rq3))))
         (Rename Nothing 
                (AChc f 
                     (thing (renameMap chcDistr rq2))
                     (thing (renameMap chcDistr rq4))))
         (CChc f c1 c2)
-- f<q₁ ∪ q₂, q₃ ∪ q₄> ≡ f<q₁, q₃> ∪ f<q₂, q₄>
chcDistr (AChc f (SetOp Union q1 q2) (SetOp Union q3 q4))
  = SetOp Union (AChc f (chcDistr q1) (chcDistr q3))
                (AChc f (chcDistr q2) (chcDistr q4))
-- f<q₁ ∩ q₂, q₃ ∩ q₄> ≡ f<q₁, q₃> ∩ f<q₂, q₄>
chcDistr (AChc f (SetOp Diff q1 q2) (SetOp Diff q3 q4))
  = SetOp Diff (AChc f (chcDistr q1) (chcDistr q3))
               (AChc f (chcDistr q2) (chcDistr q4))

-- | Pushes out projection as far as possible.
-- Note that you don't necessarily want to push out all projs.
-- Eg: proj l1 R * proj l2 S = proj (l1 + l2) (R * S)
--     but the rhs isn't more efficient than the lhs! keep in 
--     min that the same goes for joins.
-- There are also cases that you CANNOT push out projs:
-- Eg: proj l1 q1 `union` proj l1 q2 <> proj l1 (q1 `union` q2)
pushOutProj :: Algebra -> Algebra
pushOutProj (SetOp o q1 q2)
  = SetOp o (pushOutProj q1) (pushOutProj q2)
pushOutProj (AChc f q1 q2) 
  = AChc f (pushOutProj q1) (pushOutProj q2)
pushOutProj (Join rq1 rq2 c)
  = Join (renameMap pushOutProj rq1) (renameMap pushOutProj rq2) c
pushOutProj (Prod rq1 rq2) 
  = Prod (renameMap pushOutProj rq1) (renameMap pushOutProj rq2)
-- σ c (π l q) ≡ π l (σ c q)
pushOutProj (Sel c (Rename Nothing (Proj as rq)))
  = Proj as (Rename Nothing (Sel c (renameMap pushOutProj rq)))
-- π l₁ (π l₂ q) ≡ π l₁ q
-- checks if renaming happened in l₂ and update 
-- l₁ appropriately! also if the attribute in as1 is previously
-- projected in as2 you need to conjunct their fexps!
pushOutProj (Proj as1 (Rename Nothing (Proj as2 rq)))
  = Proj (updateAtts as1 as2) (renameMap pushOutProj rq)
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
        | attrAlias a2 == Nothing 
          && attrOfOptAttr a1 == attrOfOptAttr a2 
            = Just $ mkOpt (F.And (getFexp a1) (getFexp a2)) 
                           (Rename (attrAlias a1) ((thing . getObj) a2))
        | attrAlias a2 /= Nothing 
          && attrName a1 == (fromJust (attrAlias a2))
            = Just $ applyFuncFexp (F.And (getFexp a1)) a2
        | otherwise = Nothing

-- | applies the name alias of sub to org. i.e., sub renames the
--   attribute and so we apply it to the same attribute of org.
appAttrAlias :: OptAttribute -> OptAttribute -> OptAttribute
appAttrAlias org sub = undefined

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
-- TODO: complete the recursion!
optSel :: Algebra -> Algebra
-- σ c₁ (σ c₂ q) ≡ σ (c₁ ∧ c₂) q
optSel (Sel c1 (Rename Nothing (Sel c2 rq))) 
  = Sel (VsqlAnd c1 c2) (renameMap optSel rq)
-- σ c₁ (π l (σ c₂ q)) ≡ π l (σ (c₁ ∧ c₂) q)
optSel q@(Sel c1 (Rename Nothing (Proj as (Rename n (Sel c2 rq)))))
  | noAttRename as = Proj as (Rename n (Sel (VsqlAnd c1 c2) (renameMap optSel rq)))
  | otherwise      = q
    where
      noAttRename :: OptAttributes -> Bool
      noAttRename as = and $ fmap (isNothing . name . getObj) as
-- σ c (q₁ × q₂) ≡ q₁ ⋈\_c q₂
optSel q@(Sel c (Rename Nothing (Prod rq1 rq2)))
  | notInCond c = Join (renameMap optSel rq1) (renameMap optSel rq2) (relCond c)
  | otherwise   = q 
-- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_(c₁ ∧ c₂) q₂
optSel q@(Sel c1 (Rename Nothing (Join rq1 rq2 c2)))
  | notInCond c1 = Join rq1 rq2 (And (relCond c1) c2)
  | otherwise    = q

-- | selection distributive properties.
-- TODO: check if you can do this in place that you're forcing the renaming :
--       to be nothingyou can generalize your functions more by instead of forcing
--       the renaming to be nothing check if attributes in the condition 
--       actually use the alias, if not then it's ok to do the opt.
selDistr :: Algebra -> VariationalContext -> Schema -> Algebra
-- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ (σ c₁ q₁) ⋈\_c₂ q₂
-- or 
-- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_c₂ (σ c₁ q₂)
selDistr q@(Sel c1 (Rename Nothing (Join rq1 rq2 c2))) ctx s = undefined
  -- | !notInCond c1 = q
  -- | notInCond c1 && attsOfCondExistInEnv (relCond c1) 
-- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₁ q₁) ⋈\_c (σ c₂ q₂)
-- or 
-- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₂ q₁) ⋈\_c (σ c₁ q₂)

-- | projection distributive properties.
prjDistr :: Algebra -> Algebra
prjDistr = undefined
-- π (l₁, l₂) (q₁ ⋈\_c q₂) ≡ (π l₁ q₁) ⋈\_c (π l₂ q₂)
-- π (l₁, l₂) ((π (l₁, l₃) q₁) ⋈\_c (π (l₂, l₄))) ≡ π (l₁, l₂) (q₁ ⋈\_c q₂)


-- | choices rules.

-- | relational alg and choices combined rules.
-- chcRel :: Algebra -> Algebra
-- -- f<σ (c₁ ∧ c₂) q₁, σ (c₁ ∧ c₃) q₂> ≡ σ 
-- chcRel (AChc f (Sel (VsqlCond (And c1 c2)) rq1) (Sel (VsqlCond (And c3 c4)) rq2)) = undefined
-- chcRel (AChc f (Sel (VsqlAnd (VsqlCond c1) (VsqlCond c2)) rq1) (Sel (VsqlAnd (VsqlCond c3) (VsqlCond c4)) rq2)) = undefined
-- chcRel 








