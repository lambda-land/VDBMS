-- | Relational algebra.
module VDBMS.QueryLang.RelAlg.Relational.Algebra (

        RAlgebra(..)
        , SetOp(..)
        , module VDBMS.QueryLang.SQL.Condition

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Basics.SetOp

-- | More expressive relaitonal algebra.
--   Ie, it has renaming of attributes and subqueries in addition to 
--   qualified attributes.
data RAlgebra
   = RSetOp SetOp RAlgebra RAlgebra
   | RProj  Attributes (Rename RAlgebra)
   | RSel   (SqlCond RAlgebra) (Rename RAlgebra)
   | RJoin (Rename RAlgebra) (Rename RAlgebra) RCondition
   | RProd (Rename RAlgebra) (Rename RAlgebra)
   | RTRef  (Rename Relation)
   | REmpty
  deriving (Data,Eq,Show,Typeable,Ord)

