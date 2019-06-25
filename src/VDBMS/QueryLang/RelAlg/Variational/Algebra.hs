-- | Variational relational algebra.
module VDBMS.QueryLang.RelAlg.Variational.Algebra (

        Algebra(..),
        SetOp(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.QueryLang.RelAlg.Basics.SetOp
import VDBMS.QueryLang.RelAlg.Relational.Algebra

-- | Variational relational algebra.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  [Opt Attribute] Algebra
   | Sel   C.Condition Algebra
   | AChc  F.FeatureExpr Algebra Algebra
   | TRef  Relation
   | Empty 
  deriving (Data,Eq,Show,Typeable,Ord)

-- | More expressive variational relational algebra.
data Algebra'
   = SetOp' SetOp Algebra' Algebra' (Rename Algebra')
   | Proj'  [Opt (Rename QualifiedAttribute)] Algebra' (Rename Algebra')
   | Sel'   C.Condition Algebra' (Rename Algebra')
   | AChc'  F.FeatureExpr Algebra' (Rename Algebra') Algebra' (Rename Algebra')
   | TRef'  Relation (Rename Relation)
   | Empty' 
  deriving (Data,Eq,Show,Typeable,Ord)


instance Variational Algebra where

  type NonVariational Algebra = RAlgebra

  type Variant Algebra = Opt RAlgebra

  configure c (SetOp o l r)   = RSetOp o (configure c l) (configure c r)
  configure c (Proj as q)     = RProj (configureOptList c as) (configure c q)
  configure c (Sel cond q)    = RSel (configure c cond) (configure c q) 
  configure c (AChc f l r) 
    | F.evalFeatureExpr c f   = configure c l
    | otherwise               = configure c r
  configure c (TRef r)        = RTRef r
  configure c Empty           = REmpty

  linearize (SetOp s q1 q2) = combOpts F.And (RSetOp s) (linearize q1) (linearize q2)
  linearize (Proj as q)     = combOpts F.And RProj (groupOpts as) (linearize q)
  linearize (Sel c q)       = combOpts F.And RSel (linearize c) (linearize q)
  linearize (AChc f q1 q2)  = mapFst (F.And f) (linearize q1) ++
                              mapFst (F.And (F.Not f)) (linearize q2)
  linearize (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
  linearize Empty           = pure $ mkOpt (F.Lit True) REmpty

