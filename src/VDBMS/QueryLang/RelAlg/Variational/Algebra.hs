-- | Variational relational algebra.
module VDBMS.QueryLang.RelAlg.Variational.Algebra (

        Algebra(..)
        , OptAttributes(..)
        

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

-- | Optionalizes variational SQL conditions.
optVsqlCond :: VsqlCond -> [VariantGroup VsqlCond]
optVsqlCond (VsqlCond c)     = mapSnd SqlCond (optionalize_ c)
optVsqlCond (VsqlIn a q)     = mapSnd (SqlIn a) (optionalize_ q)
optVsqlCond (VsqlNot c)      = mapSnd SqlNot (optVsqlCond c)
optVsqlCond (VsqlOr l r)     = 
  combOpts F.And SqlOr (optVsqlCond l) (optVsqlCond r) 
optVsqlCond (VsqlAnd l r)    = 
  combOpts F.And SqlAnd (optVsqlCond l) (optVsqlCond r)
optVsqlCond (VsqlCChc f l r) = 
  mapFst (F.And f) (optVsqlCond l) ++
  mapFst (F.And (F.Not f)) (optVsqlCond r)

instance Show VsqlCond where
  show = prettySqlCond

instance Variational VsqlCond where

  type NonVariational VsqlCond = SqlCond RAlgebra
  
  configure = configureVsqlCond
  
  optionalize_ = optVsqlCond

instance Boolean VsqlCond where
  true  = VsqlCond (Lit True)
  false = VsqlCond (Lit False)
  bnot  = VsqlNot
  (&&&) = VsqlAnd
  (|||) = VsqlOr


-- | Optional attributes.
type OptAttributes = [Opt (Rename Attr)]

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

-- | Optionalizes a rename algebra.
--   Helper for optAlgebra.
optRename :: Rename Algebra -> [Opt (Rename RAlgebra)]
optRename r = mapSnd (Rename (name r)) $ optionalize_ (thing r)

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

-- | Optionalizes an algebra.
--   Note that optionalization doesn't consider schema at all. it just
--   optionalizes a query. So it doesn't group queries based on the 
--   presence condition of attributes or relations.
optAlgebra :: Algebra -> [VariantGroup Algebra]
optAlgebra (SetOp s q1 q2) = 
  combOpts F.And (RSetOp s) (optAlgebra q1) (optAlgebra q2)
optAlgebra (Proj as q)     = combOpts F.And RProj (groupOpts as) (optRename q)
optAlgebra (Sel c q)       = 
  combOpts F.And RSel (optionalize_ c) (optRename q) 
optAlgebra (AChc f q1 q2)  = mapFst (F.And f) (optAlgebra q1) ++
                             mapFst (F.And (F.Not f)) (optAlgebra q2)
optAlgebra (Join js)       = mapSnd RJoin $ opt' js
  where
    opt' :: Joins -> [Opt RJoins]
    opt' (JoinTwoTables l r c) = 
      mapSnd (\cond -> RJoinTwoTable l r cond) (optionalize_ c)
    opt' (JoinMore js r c)     = 
      combOpts F.And (\c' js' -> RJoinMore js' r c') (optionalize_ c) (opt' js)
optAlgebra (Prod r l rs)   = pure $ mkOpt (F.Lit True) (RProd r l rs)
optAlgebra (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
optAlgebra Empty           = pure $ mkOpt (F.Lit True) REmpty


instance Variational Algebra where

  type NonVariational Algebra = RAlgebra

  configure = configureAlgebra

  optionalize_ = optAlgebra

  
  

