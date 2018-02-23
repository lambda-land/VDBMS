module VDB.FeatureExpr where

import Data.Data (Data,Typeable)

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import Data.SBV

import VDB.Config
import VDB.Name
import VDB.SAT


-- | Boolean expressions over features.
data FeatureExpr
   = Lit Bool
   | Ref Feature
   | Not FeatureExpr
   | And FeatureExpr FeatureExpr
   | Or  FeatureExpr FeatureExpr
  deriving (Data,Eq,Typeable)

-- | The set of features referenced in a feature expression.
features :: FeatureExpr -> Set Feature
features (Lit _)   = Set.empty
features (Ref f)   = Set.singleton f
features (Not e)   = features e
features (And l r) = features l `Set.union` features r
features (Or  l r) = features l `Set.union` features r

-- | Evaluate a feature expression against a configuration.
evalFeatureExpr :: Boolean b => Config b -> FeatureExpr -> b
evalFeatureExpr _ (Lit b)   = if b then true else false
evalFeatureExpr c (Ref f)   = c f
evalFeatureExpr c (Not e)   = bnot (evalFeatureExpr c e)
evalFeatureExpr c (And l r) = evalFeatureExpr c l &&& evalFeatureExpr c r
evalFeatureExpr c (Or  l r) = evalFeatureExpr c l ||| evalFeatureExpr c r

-- | Pretty print a feature expression.
prettyFeatureExpr :: FeatureExpr -> String
prettyFeatureExpr = top
  where
    top (And l r) = sub l ++ "∧" ++ sub r
    top (Or  l r) = sub l ++ "∨" ++ sub r
    top e         = sub e
    sub (Lit b)   = if b then "#T" else "#F"
    sub (Ref f)   = featureName f
    sub (Not e)   = "¬" ++ sub e
    sub e         = "(" ++ top e ++ ")"

-- | Generate a symbolic predicate for a feature expression.
symbolicFeatureExpr :: FeatureExpr -> Predicate
symbolicFeatureExpr e = do
    let fs = Set.toList (features e)
    syms <- fmap (Map.fromList . zip fs) (sBools (map featureName fs))
    let look f = fromMaybe err (Map.lookup f syms)
    return (evalFeatureExpr look e)
  where err = error "symbolicFeatureExpr: Internal error, no symbol found."

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
shrinkFeatureExpr (Or l r)
    | unsatisfiable l           = shrinkFeatureExpr r
    | unsatisfiable r           = shrinkFeatureExpr l
shrinkFeatureExpr e = e

instance Boolean FeatureExpr where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or

instance SAT FeatureExpr where
  toPredicate = symbolicFeatureExpr

instance Show FeatureExpr where
  show = prettyFeatureExpr
