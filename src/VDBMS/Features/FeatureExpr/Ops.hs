-- | Feature expression ops that rely on the SAT solver.
module VDBMS.Features.FeatureExpr.Ops (

        tautImplyFexps,
        selectFeatureExpr,
        shrinkFeatureExpr

) where

import Data.SBV
import VDBMS.Features.Feature
import VDBMS.Features.FeatureExpr.Types
import VDBMS.Features.FeatureExpr.Core (imply)
import VDBMS.Features.FeatureExpr.Instances
import VDBMS.Features.SAT

-- | Determines if f is more general than f'.
tautImplyFexps :: FeatureExpr -> FeatureExpr -> Bool
tautImplyFexps f f' = tautology $ imply f f' 


-- | Select a feature within a feature expressions, potentially simplifying it.
selectFeatureExpr :: Feature -> Bool -> FeatureExpr -> FeatureExpr
selectFeatureExpr f b e = shrinkFeatureExpr (select e)
  where
    select e@(Lit _)  = e
    select e@(Ref f')
        | f == f'     = if b then true else false
        | otherwise   = e
    select (Not e)    = Not (select e)
    select (And l r)  = And (select l) (select r)
    select (Or  l r)  = Or  (select l) (select r)

-- | Reduce the size of a feature expression by applying some basic
--   simplification rules.
shrinkFeatureExpr :: FeatureExpr -> FeatureExpr
shrinkFeatureExpr e
    | unsatisfiable e           = Lit False
    | tautology e               = Lit True
shrinkFeatureExpr (Not (Not e)) = shrinkFeatureExpr e
shrinkFeatureExpr (And l r)
    | tautology l               = shrinkFeatureExpr r
    | tautology r               = shrinkFeatureExpr l
    | otherwise                 = And (shrinkFeatureExpr l) (shrinkFeatureExpr r)
shrinkFeatureExpr (Or l r)
    | unsatisfiable l           = shrinkFeatureExpr r
    | unsatisfiable r           = shrinkFeatureExpr l
    | otherwise                 = Or (shrinkFeatureExpr l) (shrinkFeatureExpr r)
shrinkFeatureExpr e = e

