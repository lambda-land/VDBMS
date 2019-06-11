-- | Variational relational algebra.
module VDBMS.QueryLang.Variational.Algebra (

        Algebra(..),
        SetOp(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.Variational.Condition
import VDBMS.QueryLang.Basics.SetOp

data Att = OptAtt FeatureExpr Attribute

-- data OptionalAtts = OptAtts OptionalAtts OptionalAtt
--    | OneOptAtt OptionalAtt

-- | Variational relational algebra.
--   Note that a query such as TRef R isn't acceptable
--   because a query must use projection to project
--   desirable attributes. This is important for the 
--   App1 translation rules.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  [Opt Attribute] Algebra
   -- | Proj OptionalAtts Algebra
   | Sel   Condition Algebra
   | AChc  FeatureExpr Algebra Algebra
   | TRef  Relation
   | Empty 
  deriving (Data,Eq,Show,Typeable,Ord)

-- instance Variational Algebra where

--   choice = AChc

--   choiceMap g (SetOp o l r) = SetOp o (choiceMap g l) (choiceMap g r)
--   -- the following is wrong!!!
--   choiceMap g (Proj as e)   = Proj as (choiceMap g e)
--   -- choiceMap g (Proj as e)   = Proj (configureOptListRetOpt g as) (choiceMap g e)
--   choiceMap g (Sel  c  e)   = Sel  c  (choiceMap g e)
--   choiceMap g (AChc f l r)  = g f l r
--   choiceMap _ (TRef r)      = TRef r
--   choiceMap _ Empty         = Empty

