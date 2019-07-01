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

instance Variational Condition where

  type NonVariational Condition = RCondition 

  type Variant Condition = Opt RCondition
  
  configure c (Lit b)        = RLit b
  configure c (Comp o l r)   = RComp o l r
  configure c (Not cond)     = RNot $ configure c cond
  configure c (Or l r)       = ROr (configure c l) (configure c r)
  configure c (And l r)      = RAnd (configure c l) (configure c r)
  configure c (CChc f l r) 
    | F.evalFeatureExpr c f  = configure c l
    | otherwise              = configure c r

  linearize (Lit b)        = pure $ mkOpt (F.Lit True) (RLit b)
  linearize (Comp c a1 a2) = pure $ mkOpt (F.Lit True) (RComp c a1 a2)
  linearize (Not c)        = mapSnd RNot $ linearize c
  linearize (Or c1 c2)     = combOpts F.And ROr (linearize c1) (linearize c2)
  linearize (And c1 c2)    = combOpts F.And RAnd (linearize c1) (linearize c2)
  linearize (CChc f c1 c2) = mapFst (F.And f) (linearize c1) ++
                             mapFst (F.And (F.Not f)) (linearize c2)

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
  -- bnot  = Cond . Not
  -- (&&&) = Cond . And
  -- (|||) = Cond . Or

--
-- * Variational relational algebra data type and instances.
--

-- | Variational relational algebra.
-- data Algebra
--    = SetOp SetOp Algebra Algebra
--    | Proj  [Opt Attribute] Algebra
--    | Sel   Condition Algebra
--    | AChc  F.FeatureExpr Algebra Algebra
--    | TRef  Relation
--    | Empty 
--   deriving (Data,Eq,Show,Typeable,Ord)

type RenameableOptAttr = Rename (Opt SingleAttr)

-- | Optional attributes.
data OptAttributes = OptOneAtt RenameableOptAttr
                   | OptAttList [RenameableOptAttr]
  deriving (Data,Eq,Ord,Show,Typeable)

-- | Variational conditional relational joins.
data Joins 
   = JoinTwoTables Condition (Rename Relation) (Rename Relation)
   | JoinMore      Condition Joins (Rename Relation)
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


instance Variational Algebra where

  type NonVariational Algebra = RAlgebra

  type Variant Algebra = Opt RAlgebra

  configure c (SetOp o l r)   = RSetOp o (configure c l) (configure c r)
  configure c (Proj as q)     =
    maybe REmpty (flip RProj (renameMap (configure c) q)) confedAtts
      where
        configureAtt :: Config Bool -> OptAttributes -> Maybe Attributes
        configureAtt c (OptOneAtt n)   = fmap OneAtt $ checkAtts c n 
        configureAtt c (OptAttList ns) = Just $ AttList $ catMaybes $ map (checkAtts c) ns
        checkAtts :: Config Bool -> RenameableOptAttr -> Maybe (Rename SingleAttr)
        checkAtts c n 
          | F.evalFeatureExpr c (getFexp (thing n)) 
            = Just $ Rename (name n) (getObj (thing n))
          | otherwise 
            = Nothing
        confedAtts = configureAtt c as
  configure c (Sel cond q)    = 
    RSel (configure c cond) (renameMap (configure c) q) 
  configure c (AChc f l r) 
    | F.evalFeatureExpr c f   = configure c l
    | otherwise               = configure c r
  configure c (Join js) = RJoin (configure' c js)
    where
      configure' :: Config Bool -> Joins -> RJoins
      configure' c (JoinTwoTables cond l r) = 
        RJoinTwoTable (configure c cond) l r
      configure' c (JoinMore cond js r)     = 
        RJoinMore (configure c cond) (configure' c js) r
  configure c (Prod r l rs)   = RProd r l rs
  configure c (TRef r)        = RTRef r
  configure c Empty           = REmpty

  -- Note that linearization doesn't consider schema at all. it just
  -- linearizes a query. So it doesn't group queries based on the 
  -- presence condition of attributes or relations.
  linearize (SetOp s q1 q2) = 
    combOpts F.And (RSetOp s) (linearize q1) (linearize q2)
  linearize (Proj as q)     = 
    combOpts F.And RProj (linearizeAtts as) (linearizeRename q)
      where
        linearizeAtts :: OptAttributes -> [Opt Attributes]
        linearizeAtts (OptOneAtt n)   = 
          pure $ mkOpt (getFexp (thing n)) $ OneAtt (Rename (name n) (getObj (thing n)))
        linearizeAtts (OptAttList ns) = 
          mapSnd AttList $ groupOpts $ map 
            (\n -> mkOpt (getFexp (thing n)) (Rename (name n) (getObj (thing n))))
            ns
        linearizeRename :: Rename Algebra -> [Opt (Rename RAlgebra)]
        linearizeRename r = mapSnd (Rename (name r)) $ linearize (thing r)
  linearize (Sel c q)       = 
    combOpts F.And RSel (linearize c) (linearizeRename q) 
    where
      linearizeRename :: Rename Algebra -> [Opt (Rename RAlgebra)]
      linearizeRename r = mapSnd (Rename (name r)) $ linearize (thing r)
  linearize (AChc f q1 q2)  = mapFst (F.And f) (linearize q1) ++
                              mapFst (F.And (F.Not f)) (linearize q2)
  linearize (Join js)       = mapSnd RJoin $ linearize' js
    where
      linearize' :: Joins -> [Opt RJoins]
      linearize' (JoinTwoTables c l r) = 
        mapSnd (\cond -> RJoinTwoTable cond l r) (linearize c)
      linearize' (JoinMore c js r)     = 
        combOpts F.And (\c' js' -> RJoinMore c' js' r) (linearize c) (linearize' js)
  linearize (Prod r l rs)   = pure $ mkOpt (F.Lit True) (RProd r l rs)
  linearize (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
  linearize Empty           = pure $ mkOpt (F.Lit True) REmpty


