module VDB.Condition where

import Data.Data (Data,Typeable)

import Data.SBV (Boolean(..))

import VDB.Name
import VDB.FeatureExpr (FeatureExpr)


-- | Atoms are the leaves of a condition.
data Atom
   = I Int
   | B Bool
   | S String
   | A Attribute
  deriving (Data,Eq,Show,Typeable)

-- | Comparison operators.
data CompOp = EQ | NEQ | LT | LTE | GTE | GT
  deriving (Data,Eq,Show,Typeable)

-- | Conditions.
data Condition
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc FeatureExpr Condition Condition
  deriving (Data,Eq,Show,Typeable)

instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or
