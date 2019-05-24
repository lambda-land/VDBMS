-- | Variational relational algebra.
module VDBMS.QueryLang.Algebra (

        Algebra(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.Variational.Variational
import VDBMS.QueryLang.Condition

-- | Basic set operations.
data SetOp = Union | Diff | Prod
  deriving (Data,Eq,Show,Typeable, Ord)

-- | Variational relational algebra.
--   Note that a query such as TRef R isn't acceptable
--   because a query must use projection to project
--   desirable attributes. This is important for the 
--   App1 translation rules.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  [Opt Attribute] Algebra
   | Sel   Condition Algebra
   | AChc  FeatureExpr Algebra Algebra
   | TRef  Relation
   | Empty 
  deriving (Data,Eq,Show,Typeable,Ord)

instance Variational Algebra where

  choice = AChc

  choiceMap g (SetOp o l r) = SetOp o (choiceMap g l) (choiceMap g r)
  choiceMap g (Proj as e)   = Proj as (choiceMap g e)
  choiceMap g (Sel  c  e)   = Sel  c  (choiceMap g e)
  choiceMap g (AChc f l r)  = g f l r
  choiceMap _ (TRef r)      = TRef r
  choiceMap _ Empty         = Empty

