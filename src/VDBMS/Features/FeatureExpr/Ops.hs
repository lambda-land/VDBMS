-- | Feature expression ops that rely on the SAT solver.
module VDBMS.Features.FeatureExpr.Ops (

        tautImplyFexps,
        selectFeatureExpr,
        shrinkFExp,
        shrinkFExpWRTfm,
        satAnds

) where

import Data.SBV hiding (select)
import VDBMS.Features.Feature
import VDBMS.Features.FeatureExpr.Types
import VDBMS.Features.FeatureExpr.Core (imply)
import VDBMS.Features.FeatureExpr.Instances ()
import VDBMS.Features.SAT

import Data.Generics.Uniplate.Operations (transform)

-- | Determines if f is more general than f'.
tautImplyFexps :: FeatureExpr -> FeatureExpr -> Bool
tautImplyFexps f f' = tautology $ imply f f' 

-- | checks the satisfiability of the conjunction of two fexps.
satAnds :: FeatureExpr -> FeatureExpr -> Bool
satAnds l r = satisfiable (And l r)

-- | Select a feature within a feature expressions, potentially simplifying it.
selectFeatureExpr :: Feature -> Bool -> FeatureExpr -> FeatureExpr
selectFeatureExpr f b e = shrinkFExp (select e)
  where
    select fe@(Lit _)  = fe
    select fe@(Ref f')
        | f == f'     = if b then true else false
        | otherwise   = fe
    select (Not fe)    = Not (select fe)
    select (And l r)   = And (select l) (select r)
    select (Or  l r)   = Or  (select l) (select r)

-- | reduces feature expression w.r.t how they're 
--   being generated. 
-- 
-- ¬ true ≡ false
-- ¬ false ≡ true
-- true ∧ e ≡ e
-- false ∧ e ≡ false
-- true ∨ e ≡ true
-- false ∨ e ≡ e
-- (l1 ∧ l2) ∧ r ≡ l1 ∧ (l2 ∧ r)
-- l ∧ (l ∧ r) ≡ l ∧ r
-- l ∧ l ≡ l
-- l ∨ l ≡ l
-- 
-- To test it on generated fexps try:
-- simplType empVQ1 empVSchema
-- 
shrinkFExpWRTfm :: FeatureExpr -> FeatureExpr
shrinkFExpWRTfm = factorOutFM . shrinkFExp

-- |
shrinkFExp :: FeatureExpr -> FeatureExpr
shrinkFExp = transform simpl
  where 
    simpl (Not (Lit True)) = Lit False
    simpl (Not (Lit False)) = Lit True
    simpl (And (Lit True) e) = e 
    simpl (And e (Lit True)) = e 
    simpl (And (Lit False) _) = Lit False
    simpl (And _ (Lit False)) = Lit False
    simpl (Or (Lit True) _) = Lit True
    simpl (Or _ (Lit True)) = Lit True
    simpl (Or (Lit False) e) = e 
    simpl (Or e (Lit False)) = e
    -- demorgan's law (l ∨ r) ∧ rr ≡ rr
    simpl e@(And (Or l r) rr)
      | rr == l = rr
      | r == rr = rr
      | otherwise = e
    simpl e@(And ll (Or l r))
      | ll == l = ll
      | ll == r = ll
      | otherwise = e 
    simpl (And (And l1 l2) r) = And l1 (And l2 r)
    -- simpl (And (And l1 l2) (And r1 r2))= And l1 (And l2 (And r1 r2))
    simpl (And l (And r1 r2))
      | l == r1 = And r1 r2
      | l == r2 = And r1 r2
      -- | r1 == r2 = And l r1
      | otherwise = And l (And r1 r2)
    simpl (And l r) 
      | l == r = l
      | otherwise = And l r
    simpl (Or l r)
      | l == r = l 
      | otherwise = Or l r
    -- simpl e@()
    simpl e = e
 
-- | factors out the feature model from the conjunctions 
--   in a feature expression.
factorOutFM :: FeatureExpr -> FeatureExpr
factorOutFM (And fm rest) = And fm (transform (dropFM fm) rest)
  where 
    dropFM :: FeatureExpr -> FeatureExpr -> FeatureExpr
    dropFM f (And l r) 
      | l == f = r
      | r == f = l
      | otherwise = And l r
    dropFM _ e = e
factorOutFM e = e

-- |
-- pushNeg :: FeatureExpr -> FeatureExpr
-- pushNeg e = pushNeg1 e
--   where
--     pushNeg1 (Not (Lit True)) = Lit False
--     pushNeg1 (Not (Lit False)) = Lit True
--     pushNeg1 (Not (Not e')) = pushNeg e'
--     pushNeg1 (Not (And l r)) = Or (pushNeg (Not l)) (pushNeg (Not r))
--     pushNeg1 (Not (Or l r)) = And (pushNeg (Not l)) (pushNeg (Not l))
--     pushNeg1 e' = e'

-- etst1 = Lit True 
-- etst2 = And etst1 etst1
-- eprint = Or etst2 etst3
-- etst3 = Ref "f1"
-- etst4 = And etst3 etst3
