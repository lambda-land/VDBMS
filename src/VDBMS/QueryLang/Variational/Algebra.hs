-- | Variational relational algebra.
module VDBMS.QueryLang.Variational.Algebra (

        Algebra(..),
        SetOp(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr, evalFeatureExpr)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.Variational.Condition
import VDBMS.QueryLang.Basics.SetOp
import VDBMS.QueryLang.Relational.Algebra

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

  type NonVariational Algebra = RAlgebra

  configure c (SetOp o l r) = RSetOp o (configure c l) (configure c r)
  configure c (Proj as q)   = RProj (configureOptList c as) (configure c q)
  configure c (Sel cond q)  = RSel (configure c cond) (configure c q) 
  configure c (AChc f l r) 
    | evalFeatureExpr c f   = configure c l
    | otherwise             = configure c r
  configure c (TRef r)      = RTRef r
  configure c Empty         = REmpty
