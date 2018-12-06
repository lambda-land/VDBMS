-- | Variational conditions in relational algebra and queries.
module VDB.Condition where

import Data.Data (Data,Typeable)

import Data.SBV (Boolean(..))

import VDB.FeatureExpr (FeatureExpr)
import VDB.Name
import VDB.Type
import VDB.Variational

-- | Atoms are the leaves of a condition.
data Atom
   = Val  Value
   | Attr Attribute
  deriving (Data,Eq,Show,Typeable,Ord)

-- | Variational conditions.
data Condition
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc FeatureExpr Condition Condition
  deriving (Data,Eq,Show,Typeable,Ord)

instance Variational Condition where

  choice = CChc

  choiceMap g (Not c)      = Not (choiceMap g c)
  choiceMap g (Or  l r)    = Or  (choiceMap g l) (choiceMap g r)
  choiceMap g (And l r)    = And (choiceMap g l) (choiceMap g r)
  choiceMap g (CChc f l r) = g f l r
  choiceMap _ c            = c

instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or
