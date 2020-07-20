-- | Feature expression ops that rely on the SAT solver.
module VDBMS.Features.FeatureExpr.Ops where
-- (

--         tautImplyFexps,
--         selectFeatureExpr,
--         shrinkFeatureExpr,
--         satAnds

-- ) where

import Data.SBV hiding (select)
import VDBMS.Features.Feature
import VDBMS.Features.FeatureExpr.Types
import VDBMS.Features.FeatureExpr.Core (imply)
import VDBMS.Features.FeatureExpr.Instances ()
import VDBMS.Features.SAT
-- import VDBMS.Features.FeatureExpr.Reduce

import Data.Generics.Uniplate.Operations (transform)

-- | Determines if f is more general than f'.
tautImplyFexps :: FeatureExpr -> FeatureExpr -> Bool
tautImplyFexps f f' = tautology $ imply f f' 

-- | checks the satisfiability of the conjunction of two fexps.
satAnds :: FeatureExpr -> FeatureExpr -> Bool
satAnds l r = satisfiable (And l r)

-- | Select a feature within a feature expressions, potentially simplifying it.
selectFeatureExpr :: Feature -> Bool -> FeatureExpr -> FeatureExpr
selectFeatureExpr f b e = shrinkFeatureExpr (select e)
  where
    select fe@(Lit _)  = fe
    select fe@(Ref f')
        | f == f'     = if b then true else false
        | otherwise   = fe
    select (Not fe)    = Not (select fe)
    select (And l r)   = And (select l) (select r)
    select (Or  l r)   = Or  (select l) (select r)

-- |
shrinkFeatureExpr :: FeatureExpr -> FeatureExpr
shrinkFeatureExpr = factorOutFM . transform simpl
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
    simpl e = e
  
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


-- | Reduce the size of a feature expression by applying some basic
--   simplification rules.
-- shrinkFeatureExpr :: FeatureExpr -> FeatureExpr
-- shrinkFeatureExpr e@(Lit _)    = e
-- shrinkFeatureExpr (And (Lit True) e) = shrinkFeatureExpr e
-- shrinkFeatureExpr (And e (Lit True)) = shrinkFeatureExpr e
-- shrinkFeatureExpr (And (Lit False) _) = Lit False
-- shrinkFeatureExpr (And _ (Lit False)) = Lit False
-- shrinkFeatureExpr (Or (Lit False) e) = shrinkFeatureExpr e
-- shrinkFeatureExpr (Or e (Lit False)) = shrinkFeatureExpr e
-- shrinkFeatureExpr (Or (Lit True) _) = Lit True
-- shrinkFeatureExpr (Or _ (Lit True)) = Lit True
-- shrinkFeatureExpr (Not (Not e)) = shrinkFeatureExpr e
-- shrinkFeatureExpr (Or (And l r) (And l' r'))
--     | l == l' = And (shrinkFeatureExpr l) 
--                     (Or (shrinkFeatureExpr r) (shrinkFeatureExpr r'))
--     | r == r' = And (shrinkFeatureExpr r)
--                     (Or (shrinkFeatureExpr l) (shrinkFeatureExpr l'))
--     | otherwise = Or (And (shrinkFeatureExpr l) (shrinkFeatureExpr r))
--                      (And (shrinkFeatureExpr l') (shrinkFeatureExpr r'))
-- shrinkFeatureExpr (And (Or l r) (Or l' r'))
--     | l == l' = Or (shrinkFeatureExpr l)
--                    (And (shrinkFeatureExpr r) (shrinkFeatureExpr r'))
--     | r == r' = Or (shrinkFeatureExpr r)
--                    (And (shrinkFeatureExpr l) (shrinkFeatureExpr l'))
--     | otherwise = (And (Or (shrinkFeatureExpr l) (shrinkFeatureExpr r))
--                        (Or (shrinkFeatureExpr l') (shrinkFeatureExpr r')))
-- shrinkFeatureExpr e
--     | unsatisfiable e           = Lit False
--     | tautology e               = Lit True
-- shrinkFeatureExpr (And e e)     = shrinkFeatureExpr e
-- shrinkFeatureExpr (And l r)
    -- | l == r                    = shrinkFeatureExpr l
    -- | l == Not r                = Lit False
    -- | r == Not l                = Lit False
    -- | tautology l               = shrinkFeatureExpr r
    -- | tautology r               = shrinkFeatureExpr l
    -- | otherwise                 = And (shrinkFeatureExpr l) (shrinkFeatureExpr r)
-- shrinkFeatureExpr (Or e e)      = shrinkFeatureExpr e
-- shrinkFeatureExpr (Or l r)
    -- | l == r                    = shrinkFeatureExpr l
    -- | l == Not r                = Lit True
    -- | r == Not l                = Lit True
--     | unsatisfiable l           = shrinkFeatureExpr r
--     | unsatisfiable r           = shrinkFeatureExpr l
--     | otherwise                 = Or (shrinkFeatureExpr l) (shrinkFeatureExpr r)
-- shrinkFeatureExpr e = e


-- etst1 = Lit True 
-- etst2 = And etst1 etst1
-- eprint = Or etst2 etst3
-- etst3 = Ref "f1"
-- etst4 = And etst3 etst3
