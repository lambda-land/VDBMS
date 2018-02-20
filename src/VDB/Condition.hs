module VDB.Condition where

import Data.Data (Data,Typeable)

import VDB.Name
import VDB.FeatureExpr


-- | Atoms are the leaves of a condition.
data Atom
   = I Int
   | B Bool
   | S String
   | A Attribute
  deriving (Data,Eq,Show,Typeable)

-- | Comparison operators.
data Op = LT | LTE | GTE | GT | EQ | NEQ
  deriving (Data,Eq,Show,Typeable)

-- | Conditions.
data Condition
   = Comp Op Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc FeatureExpr Condition Condition
  deriving (Data,Eq,Show,Typeable)
