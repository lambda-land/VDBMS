-- | Variational conditions in variational algebra and queries.
module VDBMS.QueryLang.RelAlg.Variational.Condition (

        Condition(..),
        Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
-- import Data.Convertible (safeConvert)
-- import qualified Data.Text as T (pack,Text)

import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Variational
import VDBMS.QueryLang.RelAlg.Basics.Atom
import VDBMS.QueryLang.RelAlg.Relational.Condition
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Variational.Opt

import Database.HDBC (SqlValue)


-- | Variational conditions.
data Condition
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | In   Attribute Algebra
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
    sub (In a q) = attributeName a ++ " IN " ++ show q
    sub c = " ( " ++ top c ++ " ) "

instance Show Condition where
  show = prettyRelCondition

instance Variational Condition where

  type NonVariational Condition = RCondition

  type Variant Condition = Opt RCondition
  
  configure c (Lit b)        = RLit b
  configure c (Comp o l r)   = RComp o l r
  configure c (Not cond)     = RNot $ configure c cond
  configure c (Or l r)       = ROr (configure c l) (configure c r)
  configure c (And l r)      = RAnd (configure c l) (configure c r)
  configure c (CChc f l r) 
    | F.evalFeatureExpr c f  = configure c l
    | otherwise              = configure c r

  linearize (Lit b)        = pure $ mkOpt (F.Lit True) (RLit b)
  linearize (Comp c a1 a2) = pure $ mkOpt (F.Lit True) (RComp c a1 a2)
  linearize (Not c)        = mapSnd RNot $ linearize c
  linearize (Or c1 c2)     = combOpts F.And ROr (linearize c1) (linearize c2)
  linearize (And c1 c2)    = combOpts F.And RAnd (linearize c1) (linearize c2)
  linearize (CChc f c1 c2) = mapFst (F.And f) (linearize c1) ++
                             mapFst (F.And (F.Not f)) (linearize c2)


instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or
