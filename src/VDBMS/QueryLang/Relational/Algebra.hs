-- | Relational algebra.
module VDBMS.QueryLang.Relational.Algebra (

        RAlgebra(..),
        SetOp(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.Relational.Condition
import VDBMS.QueryLang.Basics.SetOp

-- | Variational relational algebra.
--   Note that a query such as TRef R isn't acceptable
--   because a query must use projection to project
--   desirable attributes. This is important for the 
--   App1 translation rules.
data RAlgebra
   = RSetOp SetOp RAlgebra RAlgebra
   | RProj  [Attribute] RAlgebra
   | RSel   RCondition RAlgebra
   | RTRef  Relation
   | REmpty 
  deriving (Data,Eq,Show,Typeable,Ord)

