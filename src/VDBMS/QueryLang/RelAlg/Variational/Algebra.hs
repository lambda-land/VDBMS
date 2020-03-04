-- | Variational relational algebra.
module VDBMS.QueryLang.RelAlg.Variational.Algebra (

        Algebra(..)
        , OptAttribute
        , OptAttributes
        , VsqlCond(..)
        , module VDBMS.QueryLang.RelAlg.Basics.SetOp
        , module VDBMS.QueryLang.RelAlg.Variational.Condition 
        , attrOfOptAttr
        , attrName
        , attrAlias
        , vsqlCondEq
        , configureAlgebra_
        , pushFexp2OptAtts
        , disjFexpOptAttr
        , qualOfOptAttr
        , conjFexpOptAttr
        , numUniqueVariantQ
        , numVarintQ
        -- , optAlgebra
        

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))

import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Variational.Condition
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Features.Config (Config)
import VDBMS.Variational.Variational
import VDBMS.Variational.Opt
import VDBMS.QueryLang.RelAlg.Basics.SetOp
import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.Features.SAT (equivalent)
import VDBMS.VDB.Schema.Relational.Lookups (rlookupAttsList)
import VDBMS.VDB.Schema.Variational.Schema 

-- import Data.Set (Set)
import qualified Data.Set as Set

--
-- * Variaitonal sql condition data type and instances.
--

-- | Variational Sql conditions.
data VsqlCond
   = VsqlCond Condition
   | VsqlIn   Attr Algebra
   | VsqlNot  VsqlCond
   | VsqlOr   VsqlCond VsqlCond
   | VsqlAnd  VsqlCond VsqlCond
   | VsqlCChc F.FeatureExpr VsqlCond VsqlCond
  deriving (Data,Typeable)

-- | Vsqlcond equivalence.
vsqlCondEq :: VsqlCond -> VsqlCond -> Bool
vsqlCondEq (VsqlCond c1) (VsqlCond c2) = conditionEq c1 c2
vsqlCondEq (VsqlIn a1 q1) (VsqlIn a2 q2) 
  = a1 == a2 && q1 == q2 
vsqlCondEq (VsqlNot c1) (VsqlNot c2) = vsqlCondEq c1 c2 
vsqlCondEq (VsqlNot c1) (VsqlCond (Not c2)) 
  = vsqlCondEq c1 (VsqlCond c2)
vsqlCondEq (VsqlCond (Not c1)) (VsqlNot c2) 
  = vsqlCondEq (VsqlCond c1) c2
vsqlCondEq (VsqlOr r1 l1) (VsqlOr r2 l2) 
  = (vsqlCondEq r1 r2 && vsqlCondEq l1 l2)
 || (vsqlCondEq r1 l2 && vsqlCondEq l1 r2)
vsqlCondEq (VsqlOr r1 l1) (VsqlCond (Or r2 l2)) 
  = (vsqlCondEq r1 (VsqlCond r2) && vsqlCondEq l1 (VsqlCond l2))
 || (vsqlCondEq r1 (VsqlCond l2) && vsqlCondEq l1 (VsqlCond r2))
vsqlCondEq (VsqlCond (Or r1 l1)) (VsqlOr r2 l2)
  = (vsqlCondEq (VsqlCond r1) r2 && vsqlCondEq (VsqlCond l1) l2)
 || (vsqlCondEq (VsqlCond r1) l2 && vsqlCondEq (VsqlCond l1) r2) 
vsqlCondEq (VsqlAnd r1 l1) (VsqlAnd r2 l2) 
  = (vsqlCondEq r1 r2 && vsqlCondEq l1 l2)
 || (vsqlCondEq r1 l2 && vsqlCondEq l1 r2)
vsqlCondEq (VsqlAnd r1 l1) (VsqlCond (And r2 l2))
  = (vsqlCondEq r1 (VsqlCond r2) && vsqlCondEq l1 (VsqlCond l2))
 || (vsqlCondEq r1 (VsqlCond l2) && vsqlCondEq l1 (VsqlCond r2))
vsqlCondEq (VsqlCond (And r1 l1)) (VsqlAnd r2 l2)
  = (vsqlCondEq (VsqlCond r1) r2 && vsqlCondEq (VsqlCond l1) l2)
 || (vsqlCondEq (VsqlCond r1) l2 && vsqlCondEq (VsqlCond l1) r2)
vsqlCondEq (VsqlCChc f1 r1 l1) (VsqlCChc f2 r2 l2) 
  = equivalent f1 f2 && vsqlCondEq r1 r2 && vsqlCondEq l1 l2
vsqlCondEq _ _ = False

instance Eq VsqlCond where
  (==) = vsqlCondEq

-- | pretty prints pure relational and IN conditions.
prettySqlCond :: VsqlCond -> String
prettySqlCond (VsqlCond (CChc _ _ _)) = error "cannot pretty print a choice of relational conditions!!"
prettySqlCond (VsqlCChc _ _ _) = error "cannot pretty print a choice of SQL conditions!!"
prettySqlCond c = top c
  where
    top (VsqlCond r) = show r
    top (VsqlOr l r) = sub l ++ " OR " ++ sub r 
    top (VsqlAnd l r) = sub l ++ " AND " ++ sub r
    top cond = sub cond
    sub (VsqlIn a q) = attributeName (attribute a) ++ " IN ( " ++ show q ++ " ) "
    sub (VsqlNot cond) = " NOT " ++ sub cond
    sub cond = " ( " ++ top cond ++ " ) "

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

-- | Optional attribute.
type OptAttribute = Opt (Rename Attr)

-- | conjuncts a feature expr with attribute's pc.
conjFexpOptAttr :: F.FeatureExpr -> OptAttribute -> OptAttribute
conjFexpOptAttr f = applyFuncFexp (F.And f) 

-- | disjuncts a feature expr with attribute's pc.
disjFexpOptAttr :: F.FeatureExpr -> OptAttribute -> OptAttribute
disjFexpOptAttr f = applyFuncFexp (F.Or f)

-- | Gets the original attribute out of optattr.
attrOfOptAttr :: OptAttribute -> Attribute 
attrOfOptAttr = attribute . thing . getObj

-- | Gets the attribute name out of optattr.
attrName :: OptAttribute -> String
attrName = attributeName . attrOfOptAttr

-- | Alias of optattr.
attrAlias :: OptAttribute -> Alias
attrAlias = name . getObj 

-- | opt attr qualifier. 
qualOfOptAttr :: OptAttribute -> Maybe Qualifier 
qualOfOptAttr = qualifier . thing . getObj

-- | Optional attributes.
type OptAttributes = [OptAttribute]

-- | pushes a fexp to all optatts in the list.
pushFexp2OptAtts :: F.FeatureExpr -> OptAttributes -> OptAttributes
pushFexp2OptAtts f = map (conjFexpOptAttr f)

-- | More expressive variational relational algebra.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  OptAttributes (Rename Algebra)
   | Sel   VsqlCond (Rename Algebra)
   | AChc  F.FeatureExpr Algebra Algebra
   | Join  (Rename Algebra) (Rename Algebra) Condition
   | Prod  (Rename Algebra) (Rename Algebra)
   | TRef  (Rename Relation)
   | Empty 
  deriving (Data,Eq,Show,Typeable)

-- | Optionalizes a rename algebra.
--   Helper for optAlgebra.
optRename :: Rename Algebra -> [Opt (Rename RAlgebra)]
optRename r = mapSnd (Rename (name r)) $ optionalize_ (thing r)

-- | Configures an algebra.
configureAlgebra :: Config Bool -> Algebra -> RAlgebra
configureAlgebra c (SetOp o l r)   
  = RSetOp o (configureAlgebra c l) (configureAlgebra c r)
configureAlgebra c (Proj as q)     
  | confedAtts == [] = REmpty
  | otherwise        = RProj confedAtts (renameMap (configureAlgebra c) q)
    where
      confedAtts = configureOptList c as 
configureAlgebra c (Sel cond q)     
  = RSel (configure c cond) (renameMap (configureAlgebra c) q) 
configureAlgebra c (AChc f l r) 
  | F.evalFeatureExpr c f   = configureAlgebra c l
  | otherwise               = configureAlgebra c r
configureAlgebra c (Join l r cond) 
  = RJoin (renameMap (configureAlgebra c) l)
        (renameMap (configureAlgebra c) r)
        (configure c cond)
configureAlgebra c (Prod l r)       
  = RProd (renameMap (configureAlgebra c) l) 
          (renameMap (configureAlgebra c) r)
configureAlgebra _ (TRef r)        = RTRef r 
configureAlgebra _ Empty           = REmpty

-- | returns the number of variants of configuring a v-query.
--   Note that it excludes REmpty queries.
numVarintQ :: Algebra -> [Config Bool] -> Int
numVarintQ q cs = length $ filter (\rq -> rq /= REmpty) $ 
  map ((flip configureAlgebra) q) cs

-- | configure a query wrt the schema.
configureAlgebra_ :: Config Bool -> Schema -> Algebra -> RAlgebra
configureAlgebra_ c s (SetOp o l r) 
  = RSetOp o (configureAlgebra_ c s l) (configureAlgebra_ c s r)
configureAlgebra_ c s (Proj as rq) 
  | confedAtts == [] = REmpty
  | otherwise        = RProj confedAtts (renameMap (configureAlgebra_ c s) rq)
    where
      confedAtts = configureOptList c as 
configureAlgebra_ c s (Sel cond rq) 
  = RSel (configure c cond) (renameMap (configureAlgebra_ c s) rq) 
configureAlgebra_ c s (AChc f l r) 
  | F.evalFeatureExpr c f   = configureAlgebra_ c s l
  | otherwise               = configureAlgebra_ c s r
configureAlgebra_ c s (Join rl rr cond) 
  = RJoin (renameMap (configureAlgebra_ c s) rl)
          (renameMap (configureAlgebra_ c s) rr)
          (configure c cond)
configureAlgebra_ c s (Prod rl rr) 
  = RProd (renameMap (configureAlgebra_ c s) rl) 
          (renameMap (configureAlgebra_ c s) rr)
configureAlgebra_ c s (TRef r) 
  | check = RTRef r
  | otherwise = RProj (fmap (\a -> Rename Nothing (Attr a Nothing)) ras) 
                      (Rename Nothing (RTRef r))
    where
      check = Set.fromList vas == Set.fromList ras
      vas = maybe [] id (lookupRelAttsList (thing r) s)
      ras = maybe [] id (rlookupAttsList (thing r) confedsch)
      confedsch = configure c s 
configureAlgebra_ _ _ Empty = REmpty

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
optAlgebra (Join l r c)    = 
  combOpts F.And constRJoin (combRenameAlgs l r) (optionalize_ c)
    where 
      combRenameAlgs rl rr = combOpts F.And (,) (optRename rl) (optRename rr)
      constRJoin (rq1,rq2) cond = RJoin rq1 rq2 cond
optAlgebra (Prod l r)      = 
  combOpts F.And RProd (optRename l) (optRename r)
optAlgebra (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
optAlgebra Empty           = pure $ mkOpt (F.Lit True) REmpty

-- | returns the number of unique variants of v-query.
--   Note that it excludes REmpty queries.
numUniqueVariantQ :: Algebra -> Int 
numUniqueVariantQ q = length $ filter (\(_,rq) -> rq /= REmpty) $ optAlgebra q

instance Variational Algebra where

  type NonVariational Algebra = RAlgebra

  configure = configureAlgebra

  optionalize_ = optAlgebra

  
  

