-- | Variational relational condition.
module VDBMS.QueryLang.RelAlg.Variational.Condition (

        Condition(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))

import VDBMS.QueryLang.RelAlg.Basics.Atom
import VDBMS.QueryLang.SQL.Condition
import VDBMS.DBMS.Value.Value
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Features.Config (Config)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt

-- | Variational relational conditions.
data Condition 
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc F.FeatureExpr Condition Condition
  deriving (Data,Eq,Typeable,Ord)

-- | pretty prints pure relational conditions.
prettyRelCondition :: Condition -> String
prettyRelCondition (CChc _ _ _) = error "cannot pretty print a choice of conditions!!"
prettyRelCondition c = top c
  where
    top (Comp c l r) = show l ++ show c ++ show r
    top (And l r) = sub l ++ " AND " ++ sub r
    top (Or l r) = sub l ++ " OR " ++ sub r
    top c = sub c
    sub (Lit b) = if b then " true " else " false "
    sub (Not c) = " NOT " ++ sub c
    sub c = " ( " ++ top c ++ " ) "

instance Show Condition where
  show = prettyRelCondition

-- | configures a condition.
configureCondition :: Config Bool -> Condition -> RCondition
configureCondition c (Lit b)        = RLit b
configureCondition c (Comp o l r)   = RComp o l r
configureCondition c (Not cond)     = RNot $ configureCondition c cond
configureCondition c (Or l r)       = 
  ROr (configureCondition c l) (configureCondition c r)
configureCondition c (And l r)      = 
  RAnd (configureCondition c l) (configureCondition c r)
configureCondition c (CChc f l r) 
  | F.evalFeatureExpr c f  = configureCondition c l
  | otherwise              = configureCondition c r

-- | optionalizes a condition.
optCondition :: Condition -> [VariantGroup Condition]
optCondition (Lit b)        = pure $ mkOpt (F.Lit True) (RLit b)
optCondition (Comp c a1 a2) = pure $ mkOpt (F.Lit True) (RComp c a1 a2)
optCondition (Not c)        = mapSnd RNot $ optCondition c
optCondition (Or c1 c2)     = 
  combOpts F.And ROr (optCondition c1) (optCondition c2)
optCondition (And c1 c2)    = 
  combOpts F.And RAnd (optCondition c1) (optCondition c2)
optCondition (CChc f c1 c2) = 
  mapFst (F.And f) (optCondition c1) ++
  mapFst (F.And (F.Not f)) (optCondition c2)

instance Variational Condition where

  type NonVariational Condition = RCondition 

  configure = configureCondition

  optionalize_ = optCondition

  -- linearize = undefined


instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or

