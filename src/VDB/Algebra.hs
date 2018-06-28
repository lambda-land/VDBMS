-- | Variational relational algebra.
module VDB.Algebra where

import Data.Data (Data,Typeable)

import VDB.Name
import VDB.FeatureExpr (FeatureExpr)
import VDB.Variational
import VDB.Condition

-- | Basic set operations.
data SetOp = Union | Diff | Prod
  deriving (Data,Eq,Show,Typeable)

-- | Variational relational algebra.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  [Opt Attribute] Algebra
   | Sel   Condition Algebra
   | AChc  FeatureExpr Algebra Algebra
   | TRef  Relation
   | Empty 
  deriving (Data,Eq,Show,Typeable)


instance Variational Algebra where

  choice = AChc

  choiceMap g (SetOp o l r) = SetOp o (choiceMap g l) (choiceMap g r)
  choiceMap g (Proj as e)   = Proj as (choiceMap g e)
  choiceMap g (Sel  c  e)   = Sel  c  (choiceMap g e)
  choiceMap g (AChc f l r)  = g f l r
  choiceMap _ (TRef r)      = TRef r
  choiceMap _ Empty         = Empty
  select = undefined

  configure = undefined



