-- | Relational algebra.
module VDBMS.QueryLang.RelAlg.Relational.Algebra (

        RAlgebra(..),
        SetOp(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.RelAlg.Relational.Condition
import VDBMS.QueryLang.RelAlg.Basics.SetOp

-- | Relational algebra.
data RAlgebra
   = RSetOp SetOp RAlgebra RAlgebra
   | RProj  [Attribute] RAlgebra
   | RSel   RCondition RAlgebra
   | RTRef  Relation
   | REmpty 
  deriving (Data,Eq,Show,Typeable,Ord)


-- | More expressive relaitonal algebra.
--   Ie, it has renaming of attributes and subqueries in addition to 
--   qualified attributes.
-- Discuss at meeting Jun 26.
data RAlgebra'
   = RSetOp' SetOp RAlgebra' (Rename RAlgebra') RAlgebra' (Rename RAlgebra')
   | RProj'  [Rename QualifiedAttribute] RAlgebra' (Rename RAlgebra')
   | RSel'   RCondition RAlgebra' (Rename RAlgebra')
   | RTRef'  Relation (Rename Relation)
   | REmpty' 
  deriving (Data,Eq,Show,Typeable,Ord)

