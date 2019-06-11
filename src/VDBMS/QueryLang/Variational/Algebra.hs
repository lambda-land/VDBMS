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
  -- type Configr Algebra = Config Bool 

  configure c (SetOp o l r) = RSetOp o (configure c l) (configure c r)
  configure c (Proj as q)   = RProj (configureOptList c as) (configure c q)
  configure c (Sel cond q)  = RSel (configure c cond) (configure c q) 
  configure c (AChc f l r) 
    | evalFeatureExpr c f   = configure c l
    | otherwise             = configure c r
  configure c (TRef r)      = RTRef r
  configure c Empty         = REmpty
  -- choice = AChc

  -- choiceMap g (SetOp o l r) = SetOp o (choiceMap g l) (choiceMap g r)
  -- -- the following is wrong!!!
  -- choiceMap g (Proj as e)   = Proj as (choiceMap g e)
  -- -- choiceMap g (Proj as e)   = Proj (configureOptListRetOpt g as) (choiceMap g e)
  -- choiceMap g (Sel  c  e)   = Sel  c  (choiceMap g e)
  -- choiceMap g (AChc f l r)  = g f l r
  -- choiceMap _ (TRef r)      = TRef r
  -- choiceMap _ Empty         = Empty

-- configureVquery (SetOp o l r)  c = SetOp o (configureVquery l c) (configureVquery r c) 
-- configureVquery (Proj as q)    c = Proj (configureOptListRetOpt c as) (configureVquery q c)
-- configureVquery (Sel cond q)   c = Sel (configure c cond) (configureVquery q c)
-- configureVquery q@(AChc _ _ _) c = configureVquery (configure c q) c
-- configureVquery (TRef r)       _ = TRef r
-- configureVquery Empty          _ = Empty








