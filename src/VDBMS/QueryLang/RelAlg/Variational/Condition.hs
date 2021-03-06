-- | Variational relational condition.
module VDBMS.QueryLang.RelAlg.Variational.Condition (

        Condition(..)
        , Atom(..)
        , conditionEq

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))

import VDBMS.QueryLang.RelAlg.Basics.Atom
import VDBMS.QueryLang.SQL.Condition
import VDBMS.DBMS.Value.Value ()
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Features.Config (Config)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.Features.SAT (equivalent)

import Prelude hiding (Ordering(..))

import Data.Generics.Uniplate.Direct
import Data.Generics.Str

-- | Variational relational conditions.
data Condition 
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc F.FeatureExpr Condition Condition
  deriving (Data,Typeable)

-- | condition equivalenc.
conditionEq :: Condition -> Condition -> Bool
conditionEq (Lit b1)         (Lit b2) = b1 == b2 
conditionEq (Comp EQ r1 l1)  (Comp EQ r2 l2) 
  = (r1 == r2 && l1 == l2) || (r1 == l2 && l1 == r2)
conditionEq (Comp NEQ r1 l1) (Comp NEQ r2 l2) 
  = (r1 == r2 && l1 == l2) || (r1 == l2 && l1 == r2)
conditionEq (Comp LT r1 l1)  (Comp LT r2 l2) 
  = r1 == r2 && l1 == l2
conditionEq (Comp LT r1 l1)  (Comp GTE r2 l2) 
  = r1 == l2 && l1 == r2
conditionEq (Comp LTE r1 l1) (Comp LTE r2 l2) 
  = r1 == r2 && l1 == l2
conditionEq (Comp LTE r1 l1) (Comp GT r2 l2) 
  = r1 == l2 && l1 == r2
conditionEq (Comp GTE r1 l1) (Comp GTE r2 l2) 
  = r1 == r2 && l1 == l2
conditionEq (Comp GTE r1 l1) (Comp LT r2 l2) 
  = r1 == l2 && l1 == r2
conditionEq (Comp GT r1 l1)  (Comp GT r2 l2) 
  = r1 == r2 && l1 == l2
conditionEq (Comp GT r1 l1)  (Comp LTE r2 l2) 
  = r1 == l2 && l1 == r2
conditionEq (Not c1)         (Not c2) = conditionEq c1 c2
conditionEq (Or r1 l1)       (Or r2 l2) 
  = (conditionEq r1 r2 && conditionEq l1 l2)
 || (conditionEq r1 l2 && conditionEq l1 r2)
conditionEq (And r1 l1)      (And r2 l2) 
  = (conditionEq r1 r2 && conditionEq l1 l2)
 || (conditionEq r1 l2 && conditionEq l1 r2)
conditionEq (CChc f1 r1 l1)  (CChc f2 r2 l2) 
  = equivalent f1 f2 && conditionEq r1 r2 && conditionEq l1 l2
conditionEq _ _ = False

instance Eq Condition where
  (==) = conditionEq

-- | pretty prints pure relational conditions.
prettyRelCondition :: Condition -> String
prettyRelCondition (CChc _ _ _) = error "cannot pretty print a choice of conditions!!"
prettyRelCondition c = top c
  where
    top (Comp o l r) = show l ++ show o ++ show r
    top (And l r) = sub l ++ " AND " ++ sub r
    top (Or l r) = sub l ++ " OR " ++ sub r
    top cond = sub cond
    sub (Lit b) = if b then " true " else " false "
    sub (Not cond) = " NOT " ++ sub cond
    sub cond = " ( " ++ top cond ++ " ) "

instance Show Condition where
  show = prettyRelCondition

-- | configures a condition.
configureCondition :: Config Bool -> Condition -> RCondition
configureCondition _ (Lit b)        = RLit b
configureCondition _ (Comp o l r)   = RComp o l r
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


instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or


-- | Uniplate of condition.
condUni :: Condition -> (Str Condition, Str Condition -> Condition)
condUni (Lit b)      = plate Lit |- b 
condUni (Comp o l r) = plate Comp |- o |- l |- r
condUni (Not c)      = plate Not |* c
condUni (Or l r)     = plate Or |* l |* r 
condUni (And l r)    = plate And |* l |* r
condUni (CChc f l r) = plate CChc |- f |* l |* r

-- | Biplate of condition to fexp.
condFexpBi :: Condition -> (Str F.FeatureExpr, Str F.FeatureExpr -> Condition)
condFexpBi (Lit b)      = plate Lit |- b 
condFexpBi (Comp o l r) = plate Comp |- o |- l |- r
condFexpBi (Not c)      = plate Not |+ c
condFexpBi (Or l r)     = plate Or |+ l |+ r 
condFexpBi (And l r)    = plate And |+ l |+ r
condFexpBi (CChc f l r) = plate CChc |* f |+ l |+ r

instance Uniplate Condition where
  uniplate = condUni

instance Biplate Condition Condition where
  biplate = plateSelf

instance Biplate Condition F.FeatureExpr where
  biplate = condFexpBi

