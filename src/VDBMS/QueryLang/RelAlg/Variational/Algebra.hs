-- | Variational relational algebra.
module VDBMS.QueryLang.RelAlg.Variational.Algebra (

        Algebra(..),
        SetOp(..),
        Condition(..),
        Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
import Data.Maybe (catMaybes)

import VDBMS.QueryLang.RelAlg.Basics.Atom
import VDBMS.QueryLang.RelAlg.Relational.Condition
import VDBMS.DBMS.Value.Value
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Features.Config (Config)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
-- import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.QueryLang.RelAlg.Basics.SetOp
import VDBMS.QueryLang.RelAlg.Relational.Algebra

--
-- * Variaitonal condition data type and instances.
--

-- | Variational relational conditions.
data Condition 
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc F.FeatureExpr Condition Condition
  deriving (Data,Eq,Typeable,Ord)

-- | Variational conditions.
data Cond
   = Cond Condition
   | In   Attribute Algebra
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
    sub c = " ( " ++ top c ++ " ) "

instance Show Condition where
  show = prettyRelCondition

-- | configures a condition.
configureCondition :: Config Bool -> Condition -> RCondition
configureCondition c (Lit b)        = RLit b
configureCondition c (Comp o l r)   = RComp o l r
configureCondition c (Not cond)     = RNot $ configureCondition c cond
configureCondition c (Or l r)       = 
  ROr (configureCondition c l) (configureCondition c r)
configureCondition c (And l r)      = 
  RAnd (configureCondition c l) (configureCondition c r)
configureCondition c (CChc f l r) 
  | F.evalFeatureExpr c f  = configureCondition c l
  | otherwise              = configureCondition c r

-- | linearizes a condition.
linearizeCondition :: Condition -> [Opt RCondition]
linearizeCondition (Lit b)        = pure $ mkOpt (F.Lit True) (RLit b)
linearizeCondition (Comp c a1 a2) = pure $ mkOpt (F.Lit True) (RComp c a1 a2)
linearizeCondition (Not c)        = mapSnd RNot $ linearizeCondition c
linearizeCondition (Or c1 c2)     = 
  combOpts F.And ROr (linearizeCondition c1) (linearizeCondition c2)
linearizeCondition (And c1 c2)    = 
  combOpts F.And RAnd (linearizeCondition c1) (linearizeCondition c2)
linearizeCondition (CChc f c1 c2) = 
  mapFst (F.And f) (linearizeCondition c1) ++
  mapFst (F.And (F.Not f)) (linearizeCondition c2)

instance Variational Condition where

  type NonVariational Condition = RCondition 

  type Variant Condition = Opt RCondition
  
  configure = configureCondition

  linearize = linearizeCondition


instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or

-- | pretty prints pure relational and IN conditions.
prettyRelCond :: Cond -> String
prettyRelCond (Cond (CChc _ _ _)) = error "cannot pretty print a choice of conditions!!"
prettyRelCond c = top c
  where
    top (Cond r) = prettyRelCondition r
    top c = sub c
    sub (In a q) = attributeName a ++ " IN ( " ++ show q ++ " ) "
    sub c = " ( " ++ top c ++ " ) "

instance Show Cond where
  show = prettyRelCond

instance Variational Cond where

  type NonVariational Cond = RCond RAlgebra

  type Variant Cond = Opt (RCond RAlgebra)
  
  configure c (Cond cond) = RCond $ configure c cond
  configure c (In a q)    = RIn a (configure c q)
  
  linearize (Cond c) = mapSnd RCond (linearize c)
  linearize (In a q) = mapSnd (RIn a) (linearize q)

instance Boolean Cond where
  true  = Cond (Lit True)
  false = Cond (Lit False)
  bnot  (Cond b) = Cond (Not b)
  (&&&) (Cond l) (Cond r) = Cond (And l r)
  (|||) (Cond l) (Cond r) = Cond (Or l r)


-- | Optional attributes.
type OptAttributes = [Opt (Rename SingleAttr)]

-- | Variational conditional relational joins.
data Joins 
   = JoinTwoTables (Rename Relation) (Rename Relation) Condition
   | JoinMore      Joins             (Rename Relation) Condition
  deriving (Data,Eq,Show,Typeable,Ord)

-- | More expressive variational relational algebra.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  OptAttributes (Rename Algebra)
   | Sel   Cond (Rename Algebra)
   | AChc  F.FeatureExpr Algebra Algebra
   | Join  Joins
   | Prod  (Rename Relation) (Rename Relation) [Rename Relation]
   | TRef  (Rename Relation)
   | Empty 
  deriving (Data,Eq,Show,Typeable,Ord)

-- | Linearizes a rename algebra.
--   Helper for linearizeAlgebra.
linearizeRename :: Rename Algebra -> [Opt (Rename RAlgebra)]
linearizeRename r = mapSnd (Rename (name r)) $ linearize (thing r)

-- | Configures an algebra.
configureAlgebra :: Config Bool -> Algebra -> RAlgebra
configureAlgebra c (SetOp o l r)   = RSetOp o (configureAlgebra c l) (configureAlgebra c r)
configureAlgebra c (Proj as q)     
  | confedAtts == [] = REmpty
  | otherwise        = RProj confedAtts (renameMap (configureAlgebra c) q)
    where
      confedAtts = configureOptList c as 
configureAlgebra c (Sel cond q)    = 
  RSel (configure c cond) (renameMap (configureAlgebra c) q) 
configureAlgebra c (AChc f l r) 
  | F.evalFeatureExpr c f   = configureAlgebra c l
  | otherwise               = configureAlgebra c r
configureAlgebra c (Join js) = RJoin (configure' c js)
  where
    configure' :: Config Bool -> Joins -> RJoins
    configure' c (JoinTwoTables l r cond) = 
      RJoinTwoTable l r (configure c cond)
    configure' c (JoinMore js r cond)     = 
      RJoinMore (configure' c js) r (configure c cond)
configureAlgebra c (Prod r l rs)   = RProd r l rs
configureAlgebra c (TRef r)        = RTRef r 
configureAlgebra c Empty           = REmpty

-- | Linearizes an algebra.
--   Note that linearization doesn't consider schema at all. it just
--   linearizes a query. So it doesn't group queries based on the 
--   presence condition of attributes or relations.
linearizeAlgebra :: Algebra -> [Opt RAlgebra]
linearizeAlgebra (SetOp s q1 q2) = 
  combOpts F.And (RSetOp s) (linearizeAlgebra q1) (linearizeAlgebra q2)
linearizeAlgebra (Proj as q)     = combOpts F.And RProj (groupOpts as) (linearizeRename q)
linearizeAlgebra (Sel c q)       = 
  combOpts F.And RSel (linearize c) (linearizeRename q) 
linearizeAlgebra (AChc f q1 q2)  = mapFst (F.And f) (linearizeAlgebra q1) ++
                                   mapFst (F.And (F.Not f)) (linearizeAlgebra q2)
linearizeAlgebra (Join js)       = mapSnd RJoin $ linearize' js
  where
    linearize' :: Joins -> [Opt RJoins]
    linearize' (JoinTwoTables l r c) = 
      mapSnd (\cond -> RJoinTwoTable l r cond) (linearize c)
    linearize' (JoinMore js r c)     = 
      combOpts F.And (\c' js' -> RJoinMore js' r c') (linearize c) (linearize' js)
linearizeAlgebra (Prod r l rs)   = pure $ mkOpt (F.Lit True) (RProd r l rs)
linearizeAlgebra (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
linearizeAlgebra Empty           = pure $ mkOpt (F.Lit True) REmpty


instance Variational Algebra where

  type NonVariational Algebra = RAlgebra

  type Variant Algebra = Opt RAlgebra

  configure = configureAlgebra

  linearize = linearizeAlgebra

  
  

