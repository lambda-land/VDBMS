-- | Variational relational algebra.
module VDBMS.QueryLang.RelAlg.Variational.Algebra (

        Algebra(..)
        

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
import Data.Maybe (catMaybes)

import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Variational.Condition
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Features.Config (Config)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.RelAlg.Basics.SetOp
import VDBMS.QueryLang.RelAlg.Relational.Algebra

--
-- * Variaitonal sql condition data type and instances.
--

-- | Variational Sql conditions.
data VsqlCond
   = VsqlCond Condition
   | VsqlIn   Attribute Algebra
   | VsqlNot  VsqlCond
   | VsqlOr   VsqlCond VsqlCond
   | VsqlAnd  VsqlCond VsqlCond
   | VsqlCChc F.FeatureExpr VsqlCond VsqlCond
  deriving (Data,Eq,Typeable,Ord)

-- | pretty prints pure relational and IN conditions.
prettySqlCond :: VsqlCond -> String
prettySqlCond (VsqlCond (CChc _ _ _)) = error "cannot pretty print a choice of relational conditions!!"
prettySqlCond (VsqlCChc _ _ _) = error "cannot pretty print a choice of SQL conditions!!"
prettySqlCond c = top c
  where
    top (VsqlCond r) = show r
    top (VsqlOr l r) = sub l ++ " OR " ++ sub r 
    top (VsqlAnd l r) = sub l ++ " AND " ++ sub r
    top c = sub c
    sub (VsqlIn a q) = attributeName a ++ " IN ( " ++ show q ++ " ) "
    sub (VsqlNot c) = " NOT " ++ sub c
    sub c = " ( " ++ top c ++ " ) "

-- | Configure Variational SQL conditions.
configureVsqlCond :: Config Bool -> VsqlCond -> SqlCond RAlgebra
configureVsqlCond c (VsqlCond cond) = SqlCond $ configure c cond
configureVsqlCond c (VsqlIn a q)    = SqlIn a (configure c q)
configureVsqlCond c (VsqlNot cond)  = SqlNot (configureVsqlCond c cond)
configureVsqlCond c (VsqlOr l r)    = 
  SqlOr (configureVsqlCond c l) (configureVsqlCond c r)
configureVsqlCond c (VsqlAnd l r)   = 
  SqlAnd (configureVsqlCond c l) (configureVsqlCond c r)
configureVsqlCond c (VsqlCChc f l r) 
  | F.evalFeatureExpr c f = configureVsqlCond c l 
  | otherwise             = configureVsqlCond c r

-- | Linearizes variational SQL conditions.
linearizeVsqlCond :: VsqlCond -> [Opt (SqlCond RAlgebra)]
linearizeVsqlCond (VsqlCond c)     = mapSnd SqlCond (linearize c)
linearizeVsqlCond (VsqlIn a q)     = mapSnd (SqlIn a) (linearize q)
linearizeVsqlCond (VsqlNot c)      = mapSnd SqlNot (linearizeVsqlCond c)
linearizeVsqlCond (VsqlOr l r)     = 
  combOpts F.And SqlOr (linearizeVsqlCond l) (linearizeVsqlCond r) 
linearizeVsqlCond (VsqlAnd l r)    = 
  combOpts F.And SqlAnd (linearizeVsqlCond l) (linearizeVsqlCond r)
linearizeVsqlCond (VsqlCChc f l r) = 
  mapFst (F.And f) (linearizeVsqlCond l) ++
  mapFst (F.And (F.Not f)) (linearizeVsqlCond r)

instance Show VsqlCond where
  show = prettySqlCond

instance Variational VsqlCond where

  type NonVariational VsqlCond = SqlCond RAlgebra

  type Variant VsqlCond = Opt (SqlCond RAlgebra)
  
  configure = configureVsqlCond
  
  linearize = linearizeVsqlCond

instance Boolean VsqlCond where
  true  = VsqlCond (Lit True)
  false = VsqlCond (Lit False)
  bnot  = VsqlNot
  (&&&) = VsqlAnd
  (|||) = VsqlOr


-- | Optional attributes.
type OptAttributes = [Opt (Rename QualifiedAttr)]

-- | Variational conditional relational joins.
data Joins 
   = JoinTwoTables (Rename Relation) (Rename Relation) Condition
   | JoinMore      Joins             (Rename Relation) Condition
  deriving (Data,Eq,Show,Typeable,Ord)

-- | More expressive variational relational algebra.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  OptAttributes (Rename Algebra)
   | Sel   VsqlCond (Rename Algebra)
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

  
  

