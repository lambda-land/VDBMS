-- | Variational relational algebra.
module VDBMS.QueryLang.RelAlg.Variational.Algebra (

        Algebra(..),
        SetOp(..),
        Condition(..),
        Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))

import VDBMS.QueryLang.RelAlg.Basics.Atom
import VDBMS.QueryLang.RelAlg.Relational.Condition
import VDBMS.DBMS.Value.Value
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
-- import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.QueryLang.RelAlg.Basics.SetOp
import VDBMS.QueryLang.RelAlg.Relational.Algebra

--
-- * Variaitonal condition data type and instances.
--

-- | Variational conditions.
data Condition 
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | In   Attribute Algebra
   | CChc F.FeatureExpr Condition Condition
  deriving (Data,Eq,Typeable,Ord)

-- | pretty prints pure relational conditions.
prettyRelCondition :: Condition -> String
prettyRelCondition (CChc _ _ _) = error "cannot pretty print a choice of conditions!!"
prettyRelCondition c = top c
  where
    top (Comp c l r) = show l ++ show c ++ show r
    top (And l r) = sub l ++ " AND " ++ sub r
    top (Or l r) = sub l ++ " OR " ++ sub r
    top c = sub c
    sub (Lit b) = if b then " true " else " false "
    sub (Not c) = " NOT " ++ sub c
    sub (In a q) = attributeName a ++ " IN " ++ show q
    sub c = " ( " ++ top c ++ " ) "

instance Show Condition where
  show = prettyRelCondition

instance Variational Condition where

  type NonVariational Condition = RCondition RAlgebra

  type Variant Condition = Opt (RCondition RAlgebra)
  
  configure c (Lit b)        = RLit b
  configure c (Comp o l r)   = RComp o l r
  configure c (Not cond)     = RNot $ configure c cond
  configure c (Or l r)       = ROr (configure c l) (configure c r)
  configure c (And l r)      = RAnd (configure c l) (configure c r)
  -- configure c (In a q)       = RIn a (configure c q)
  configure c (CChc f l r) 
    | F.evalFeatureExpr c f  = configure c l
    | otherwise              = configure c r

  linearize (Lit b)        = pure $ mkOpt (F.Lit True) (RLit b)
  linearize (Comp c a1 a2) = pure $ mkOpt (F.Lit True) (RComp c a1 a2)
  linearize (Not c)        = mapSnd RNot $ linearize c
  linearize (Or c1 c2)     = combOpts F.And ROr (linearize c1) (linearize c2)
  linearize (And c1 c2)    = combOpts F.And RAnd (linearize c1) (linearize c2)
  -- linearize (In a q)       = mapSnd (RIn a) (linearize q)
  linearize (CChc f c1 c2) = mapFst (F.And f) (linearize c1) ++
                             mapFst (F.And (F.Not f)) (linearize c2)

instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or

--
-- * Variational relational algebra data type and instances.
--

-- | Variational relational algebra.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  [Opt Attribute] Algebra
   | Sel   Condition Algebra
   | AChc  F.FeatureExpr Algebra Algebra
   | TRef  Relation
   | Empty 
  deriving (Data,Eq,Show,Typeable,Ord)

-- | Optional attributes.
data OptAttributes = AllAtts F.FeatureExpr
                   | OptOneAtt (Rename (Opt SingleAttr))
                   | OptAttList [Rename (Opt SingleAttr)]
  deriving (Data,Eq,Ord,Show,Typeable)

-- | More expressive variational relational algebra.
data Algebra'
   = SetOp' SetOp Algebra Algebra
   | Proj'  OptAttributes (Rename Algebra)
   | Sel'   Condition (Rename Algebra)
   | AChc'  F.FeatureExpr Algebra Algebra
   | Prod  (Rename Relation) (Rename Relation) [Rename Relation]
   | TRef'  (Rename Relation)
   | Empty' 
  deriving (Data,Eq,Show,Typeable,Ord)


-- instance Variational Algebra where

--   type NonVariational Algebra = RAlgebra

--   type Variant Algebra = Opt RAlgebra

--   configure c (SetOp o l r)   = 
--     RSetOp o (renameMap (configure c) l) (renameMap (configure c) r)
--   -- configure c (Proj as q)     = RProj (configureOptList c as) (configure c q)
--   configure c (Sel cond q)    = 
--     RSel (configure c cond) (renameMap (configure c) q) 
--   configure c (AChc f l r) 
--     | F.evalFeatureExpr c f   = configure c l
--     | otherwise               = configure c r
--   configure c (TRef r)        = RTRef r
--   configure c Empty           = REmpty

--   -- linearize (SetOp s q1 q2) = 
--   --   combOpts F.And (RSetOp s) (renameMap linearize q1) (renameMap linearize q2)
--   -- linearize (Proj as q)     = combOpts F.And RProj (groupOpts as) (linearize q)
--   -- linearize (Sel c q)       = combOpts F.And RSel (linearize c) (linearize q)
--   -- linearize (AChc f q1 q2)  = mapFst (F.And f) (linearize q1) ++
--   --                             mapFst (F.And (F.Not f)) (linearize q2)
--   linearize (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
--   linearize Empty           = pure $ mkOpt (F.Lit True) REmpty

