-- | Feature expression core operations.
module VDBMS.Features.FeatureExpr.Core (

        features,
        andNot,
        xor,
        disjFexp,
        conjFexp,
        imply,
        evalFeatureExpr, 
        featuresList

) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.SBV (Boolean, true, false, bnot, (&&&), (|||))
import Data.List

import VDBMS.Features.Config (Config)
import VDBMS.Features.Feature
import VDBMS.Features.FeatureExpr.Types

-- | The set of features referenced in a feature expression.
features :: FeatureExpr -> Set Feature
features (Lit _)   = Set.empty
features (Ref f)   = Set.singleton f
features (Not e)   = features e
features (And l r) = features l `Set.union` features r
features (Or  l r) = features l `Set.union` features r

-- |
featuresList :: FeatureExpr -> [Feature]
featuresList = Set.toList . features

-- | initializes the features of a feature expr to false in a map.
--   used to initialize all features of a database, i.e. initializing
--   features of the fexp of vschema.
--   NOTE: HAVEN'T USED IT YET!!!!
-- initFeatureMap :: Boolean b => FeatureExpr -> Map Feature b
-- initFeatureMap e = Map.fromSet (\_ -> false) (features e)

-- | l and not r.
andNot :: FeatureExpr -> FeatureExpr -> FeatureExpr
andNot l r = l `And` Not r

-- | xor.
xor :: FeatureExpr -> FeatureExpr -> FeatureExpr
xor l r = (andNot l r) `Or` (andNot r l)

-- | disjuncts a list of fexps. Note: it doesn't shrink it!!
disjFexp :: [FeatureExpr] -> FeatureExpr
disjFexp = foldl' Or (Lit False)

-- | conjuncts a list of fexps without shrinking!!
conjFexp :: [FeatureExpr] -> FeatureExpr
conjFexp = foldl' And (Lit True)

-- | Syntactic sugar: implication
imply :: FeatureExpr -> FeatureExpr -> FeatureExpr
imply f f' = Or (Not f) f'

-- | Evaluate a feature expression against a configuration.
evalFeatureExpr :: Boolean b => Config b -> FeatureExpr -> b
evalFeatureExpr _ (Lit b)   = if b then true else false
evalFeatureExpr c (Ref f)   = c f
evalFeatureExpr c (Not e)   = bnot (evalFeatureExpr c e)
evalFeatureExpr c (And l r) = evalFeatureExpr c l &&& evalFeatureExpr c r
evalFeatureExpr c (Or  l r) = evalFeatureExpr c l ||| evalFeatureExpr c r
