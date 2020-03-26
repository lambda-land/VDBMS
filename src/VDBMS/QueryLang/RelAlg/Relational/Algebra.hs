-- | Relational algebra.
module VDBMS.QueryLang.RelAlg.Relational.Algebra (

        RAlgebra(..)
        , SetOp(..)
        , module VDBMS.QueryLang.SQL.Condition

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Basics.SetOp

-- | More expressive relaitonal algebra.
--   Ie, it has renaming of attributes and subqueries in addition to 
--   qualified attributes.
data RAlgebra
   = RSetOp SetOp RAlgebra RAlgebra
   | RProj  Attributes RAlgebra
   | RSel   (SqlCond RAlgebra) RAlgebra
   | RJoin RAlgebra RAlgebra RCondition
   | RProd RAlgebra RAlgebra
   | RTRef  Relation
   | RRenameAlg Name RAlgebra
   | REmpty
  deriving (Data,Eq,Show,Typeable,Ord)

