-- | Relational algebra.
module VDBMS.QueryLang.RelAlg.Relational.Algebra (

        RAlgebra(..),
        RJoins(..),
        SetOp(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Basics.SetOp

-- | Relational algebra.
-- data RAlgebra
--    = RSetOp SetOp RAlgebra RAlgebra
--    | RProj  [Attribute] RAlgebra
--    | RSel   (RCondition RAlgebra) RAlgebra
--    | RTRef  Relation
--    | REmpty 
--   deriving (Data,Eq,Show,Typeable,Ord)

-- | Conditional relational joins.
data RJoins 
   = RJoinTwoTable (Rename Relation) (Rename Relation) RCondition 
   | RJoinMore     RJoins            (Rename Relation) RCondition 
  deriving (Data,Eq,Show,Typeable,Ord)

-- | More expressive relaitonal algebra.
--   Ie, it has renaming of attributes and subqueries in addition to 
--   qualified attributes.
data RAlgebra
   = RSetOp SetOp RAlgebra RAlgebra
   | RProj  Attributes (Rename RAlgebra)
   | RSel   (SqlCond RAlgebra) (Rename RAlgebra)
   | RJoin  RJoins
   | RProd  (Rename Relation) (Rename Relation) [Rename Relation]
   | RTRef  (Rename Relation)
   | REmpty
  deriving (Data,Eq,Show,Typeable,Ord)

