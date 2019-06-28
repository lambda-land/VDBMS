-- | Relational conditions in relational algebra and queries.
module VDBMS.QueryLang.RelAlg.Relational.Condition (

        RCondition(..),
        RCond(..),
        Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
import Data.Convertible (safeConvert)
import qualified Data.Text as T (pack,Text)

import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Variational
import VDBMS.QueryLang.RelAlg.Basics.Atom
-- import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)

import Database.HDBC (SqlValue)

-- Pure relational conditions.
data RCondition
   = RLit  Bool
   | RComp CompOp Atom Atom
   | RNot  RCondition
   | ROr   RCondition RCondition 
   | RAnd  RCondition RCondition 
  deriving (Data,Eq,Typeable,Ord)

-- | Relational/SQL conditions, depends on what language
--   you pass it.
data RCond a
   = RCond RCondition
   | RIn   Attribute a
  deriving (Data,Eq,Typeable,Ord)

-- | pretty prints pure relational conditions.
prettyRCondition :: RCondition -> String
prettyRCondition c = top c
  where
    top (RComp c l r) = show l ++ show c ++ show r
    top (RAnd l r) = sub l ++ " AND " ++ sub r
    top (ROr l r) = sub l ++ " OR " ++ sub r
    top c = sub c
    sub (RLit b) = if b then " true " else " false "
    sub (RNot c) = " NOT " ++ sub c
    -- sub (RIn a q) = attributeName a ++ " IN " ++ show q
    sub c = " ( " ++ top c ++ " ) "

instance Show RCondition where
  show = prettyRCondition


instance Boolean RCondition where
  true  = RLit True
  false = RLit False
  bnot  = RNot
  (&&&) = RAnd
  (|||) = ROr

-- | pretty prints pure relational conditions.
prettyRCond :: Show a => RCond a -> String
prettyRCond c = top c
  where
    top (RCond r) = prettyRCondition r
    top c = sub c
    sub (RIn a q) = attributeName a ++ " IN ( " ++ show q ++ " ) "
    sub c = " ( " ++ top c ++ " ) "

instance Show a => Show (RCond a) where
  show = prettyRCond


instance Boolean (RCond a) where
  true  = RCond (RLit True)
  false = RCond (RLit False)
  -- bnot  b = RCond (bnot b)
  -- (&&&) = RCond . RAnd
  -- (|||) = RCond . ROr
