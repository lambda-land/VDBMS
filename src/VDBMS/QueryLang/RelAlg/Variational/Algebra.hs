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
        -- , attrAlias
        , vsqlCondEq
        -- , configureAlgebra_ 
        , pushFexp2OptAtts
        , disjFexpOptAttr
        , qualOfOptAttr
        , conjFexpOptAttr
        , numUniqueVariantQ
        , numVariantQ
        , optAlgebra
        , updateAttsQual
        

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))

import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Variational.Condition
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.Features.ConfFexp (confs2fexp)
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

import Data.Generics.Uniplate.Direct
import Data.Generics.Str

import Data.Maybe (isNothing, fromJust)
import qualified Text.PrettyPrint as P

import Control.Arrow (first)

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
-- type OptAttribute = Opt (Rename Attr)
type OptAttribute = Opt Attr

-- | conjuncts a feature expr with attribute's pc.
conjFexpOptAttr :: F.FeatureExpr -> OptAttribute -> OptAttribute
conjFexpOptAttr f = applyFuncFexp (F.And f) 

-- | disjuncts a feature expr with attribute's pc.
disjFexpOptAttr :: F.FeatureExpr -> OptAttribute -> OptAttribute
disjFexpOptAttr f = applyFuncFexp (F.Or f)

-- | Gets the original attribute out of optattr.
attrOfOptAttr :: OptAttribute -> Attribute 
attrOfOptAttr = attribute . getObj

-- | Gets the attribute name out of optattr.
attrName :: OptAttribute -> String
attrName = attributeName . attrOfOptAttr

-- | updates the qualifier of attributes.
updateAttsQual :: (Attr -> Attr) -> OptAttributes -> OptAttributes
updateAttsQual f as = map (applyFuncObj f) as

-- | Alias of optattr.
-- attrAlias :: OptAttribute -> Alias
-- attrAlias = name . getObj 

-- | opt attr qualifier. 
qualOfOptAttr :: OptAttribute -> Maybe Qualifier 
qualOfOptAttr = qualifier . getObj

-- | Optional attributes.
type OptAttributes = [OptAttribute]

-- | pushes a fexp to all optatts in the list.
pushFexp2OptAtts :: F.FeatureExpr -> OptAttributes -> OptAttributes
pushFexp2OptAtts f = map (conjFexpOptAttr f)

-- | More expressive variational relational algebra.
data Algebra
   = SetOp SetOp Algebra Algebra
   | Proj  OptAttributes Algebra
   | Sel   VsqlCond Algebra
   | AChc  F.FeatureExpr Algebra Algebra
   | Join  Algebra Algebra Condition
   | Prod  Algebra Algebra
   | TRef  Relation
   | RenameAlg Name Algebra
   | Empty 
  deriving (Data,Eq,Typeable)

-- | Optionalizes a rename algebra.
--   Helper for optAlgebra.
-- optRename :: Rename Algebra -> [Opt (Rename RAlgebra)]
-- optRename r = mapSnd (Rename (name r)) $ optionalize_ (thing r)

-- | Configures an algebra.
configureAlgebra :: Config Bool -> Algebra -> RAlgebra
configureAlgebra c (SetOp o l r)   
  = RSetOp o (configureAlgebra c l) (configureAlgebra c r)
configureAlgebra c (Proj as q)     
  | confedAtts == [] = REmpty
  | otherwise        = RProj confedAtts (configureAlgebra c q)
    where
      confedAtts = configureOptList c as 
configureAlgebra c (Sel cond q)     
  = RSel (configure c cond) (configureAlgebra c q) 
configureAlgebra c (AChc f l r) 
  | F.evalFeatureExpr c f   = configureAlgebra c l
  | otherwise               = configureAlgebra c r
configureAlgebra c (Join l r cond) 
  = RJoin (configureAlgebra c l)
          (configureAlgebra c r)
          (configure c cond)
configureAlgebra c (Prod l r) 
  = RProd (configureAlgebra c l) 
          (configureAlgebra c r)
configureAlgebra _ (TRef r)        = RTRef r 
configureAlgebra c (RenameAlg n q) = RRenameAlg n (configureAlgebra c q)
configureAlgebra _ Empty           = REmpty

-- | returns the number of variants of configuring a v-query.
--   Note that it excludes REmpty queries.
numVariantQ :: Algebra -> [Config Bool] -> Int
numVariantQ q cs = length $ filter (\rq -> rq /= REmpty) $ 
  map ((flip configureAlgebra) q) cs

-- | Optionalizes an algebra.
--   Note that optionalization doesn't consider schema at all. it just
--   optionalizes a query. So it doesn't group queries based on the 
--   presence condition of attributes or relations.
-- TODO doesn't seem to be working correctly.
-- optAlgebra :: Algebra -> [VariantGroup Algebra]
-- optAlgebra (SetOp s q1 q2) = 
--   combOpts F.And (RSetOp s) (optAlgebra q1) (optAlgebra q2)
-- optAlgebra (Proj as q)     = 
--   combOpts F.And RProj (groupOpts as) (optAlgebra q)
-- optAlgebra (Sel c q)       = 
--   combOpts F.And RSel (optionalize_ c) (optAlgebra q) 
-- optAlgebra (AChc f q1 q2)  = 
--   mapFst (F.And f) (optAlgebra q1) ++
--   mapFst (F.And (F.Not f)) (optAlgebra q2)
-- optAlgebra (Join l r c)    = 
--   combOpts F.And constRJoin (combRenameAlgs l r) (optionalize_ c)
--     where 
--       combRenameAlgs l r = combOpts F.And (,) (optAlgebra l) (optAlgebra r)
--       constRJoin (q1,q2) cond = RJoin q1 q2 cond
-- optAlgebra (Prod l r)      = 
--   combOpts F.And RProd (optAlgebra l) (optAlgebra r)
-- optAlgebra (TRef r)        = pure $ mkOpt (F.Lit True) (RTRef r)
-- optAlgebra (RenameAlg n q) = mapSnd (RRenameAlg n) (optAlgebra q)
-- optAlgebra Empty           = pure $ mkOpt (F.Lit True) REmpty

-- | optionalizes a query given the corresponding vschema.
optAlgebra :: Schema -> Algebra -> [VariantGroup Algebra]
optAlgebra s q = groupedQs
  where
    qs = fmap (\c -> (c, configureAlgebra c q)) (schConfs s)
    groupedQs = fmap (first (confs2fexp (schFeatures s))) $ fmap pushDownFst $ groupOn snd qs

-- | returns the number of unique variants of v-query.
--   Note that it excludes REmpty queries.
numUniqueVariantQ :: Schema -> Algebra -> Int 
numUniqueVariantQ s q = length $ filter (\(_,rq) -> rq /= REmpty) $ optAlgebra s q

instance Variational Algebra where

  type NonVariational Algebra = RAlgebra

  configure = configureAlgebra

  optionalize_ = undefined
    -- optAlgebra
    -- mapFst F.shrinkFExp . optAlgebra

-- | Uniplate of vsqlCond.
vsqlcondUni :: VsqlCond -> (Str VsqlCond, Str VsqlCond -> VsqlCond)
vsqlcondUni (VsqlCond c)     = plate VsqlCond |- c
vsqlcondUni (VsqlIn a q)     = plate VsqlIn |- a |+ q
vsqlcondUni (VsqlNot c)      = plate VsqlNot |* c
vsqlcondUni (VsqlOr l r)     = plate VsqlOr |* l |* r
vsqlcondUni (VsqlAnd l r)    = plate VsqlAnd |* l |* r
vsqlcondUni (VsqlCChc f l r) = plate VsqlCChc |- f |* l |* r

-- | Biplateof vsqlcond to fexp.
vsqlcondFexpBi :: VsqlCond -> (Str F.FeatureExpr, Str F.FeatureExpr -> VsqlCond)
vsqlcondFexpBi (VsqlCond c)     = plate VsqlCond |+ c
vsqlcondFexpBi (VsqlIn a q)     = plate VsqlIn |- a |+ q
vsqlcondFexpBi (VsqlNot c)      = plate VsqlNot |+ c
vsqlcondFexpBi (VsqlOr l r)     = plate VsqlOr |+ l |+ r
vsqlcondFexpBi (VsqlAnd l r)    = plate VsqlAnd |+ l |+ r
vsqlcondFexpBi (VsqlCChc f l r) = plate VsqlCChc |* f |+ l |+ r

-- | Biplate of vsqlcond to condition.
vsqlcondCondBi :: VsqlCond -> (Str Condition, Str Condition -> VsqlCond)
vsqlcondCondBi (VsqlCond c)     = plate VsqlCond |* c
vsqlcondCondBi (VsqlIn a q)     = plate VsqlIn |- a |+ q
vsqlcondCondBi (VsqlNot c)      = plate VsqlNot |+ c
vsqlcondCondBi (VsqlOr l r)     = plate VsqlOr |+ l |+ r
vsqlcondCondBi (VsqlAnd l r)    = plate VsqlAnd |+ l |+ r
vsqlcondCondBi (VsqlCChc f l r) = plate VsqlCChc |- f |+ l |+ r

-- | Uniplate of algebra.
algUni :: Algebra -> (Str Algebra, Str Algebra -> Algebra)  
algUni (SetOp o l r)   = (Two (One l) (One r), \(Two (One l) (One r)) -> SetOp o l r)
algUni (Proj oas q)    = (One q, \(One q) -> Proj oas q)
algUni (Sel c q)       = (One q, \(One q) -> Sel c q)
algUni (AChc f l r)    = (Two (One l) (One r), \(Two (One l) (One r)) -> AChc f l r)
algUni (Join l r c)    = plate Join |* l |* r |- c
-- (Two (One l) (One r), \(Two (One l) (One r)) -> Join l r c)
algUni (Prod l r)      = (Two (One l) (One r), \(Two (One l) (One r)) -> Prod l r)
algUni (TRef r)        = (Zero, \Zero -> TRef r)
algUni (RenameAlg n q) = (One q, \(One q) -> RenameAlg n q)
algUni Empty           = (Zero, \Zero -> Empty)


-- | Biplate of algebra to vsqlcond.
algVsqlcondBi :: Algebra -> (Str VsqlCond, Str VsqlCond -> Algebra)
algVsqlcondBi (SetOp o l r)   = plate SetOp |- o |+ l |+ r
algVsqlcondBi (Proj oas q)    = plate Proj |- oas |+ q
algVsqlcondBi (Sel c q)       = plate Sel |* c |+ q
algVsqlcondBi (AChc f l r)    = plate AChc |- f |+ l |+ r
algVsqlcondBi (Join l r c)    = plate Join |+ l |+ r |- c
algVsqlcondBi (Prod l r)      = plate Prod |+ l |+ r
algVsqlcondBi (TRef r)        = plate TRef |- r
algVsqlcondBi (RenameAlg n q) = plate RenameAlg |- n |+ q
algVsqlcondBi Empty           = plate Empty

-- | Biplate of algebra to condition.
algCondBi :: Algebra -> (Str Condition, Str Condition -> Algebra)
algCondBi (SetOp o l r)   = plate SetOp |- o |+ l |+ r
algCondBi (Proj oas q)    = plate Proj |- oas |+ q
algCondBi (Sel c q)       = plate Sel |+ c |+ q
algCondBi (AChc f l r)    = plate AChc |- f |+ l |+ r
algCondBi (Join l r c)    = plate Join |+ l |+ r |* c
algCondBi (Prod l r)      = plate Prod |+ l |+ r
algCondBi (TRef r)        = plate TRef |- r
algCondBi (RenameAlg n q) = plate RenameAlg |- n |+ q
algCondBi Empty           = plate Empty

-- | Biplate of algebra to fexp.
algFexpBi :: Algebra -> (Str F.FeatureExpr, Str F.FeatureExpr -> Algebra)
algFexpBi (SetOp o l r)   = plate SetOp |- o |+ l |+ r
algFexpBi (Proj oas q)    = plate Proj ||+ oas |+ q
algFexpBi (Sel c q)       = plate Sel |+ c |+ q
algFexpBi (AChc f l r)    = plate AChc |* f |+ l |+ r
algFexpBi (Join l r c)    = plate Join |+ l |+ r |+ c
algFexpBi (Prod l r)      = plate Prod |+ l |+ r
algFexpBi (TRef r)        = plate TRef |- r
algFexpBi (RenameAlg n q) = plate RenameAlg |- n |+ q
algFexpBi Empty           = plate Empty

-- | Uniplate of optatt.
optAttUni :: OptAttribute -> (Str OptAttribute, Str OptAttribute -> OptAttribute)
optAttUni a = (Zero, \Zero -> a)

-- | Biplate of algebra and optAtt.
algAttBi :: Algebra -> (Str OptAttribute, Str OptAttribute -> Algebra)
algAttBi (SetOp o l r)   = plate SetOp |- o |+ l |+ r
algAttBi (Proj oas q)    = plate Proj ||+ oas |+ q
algAttBi (Sel c q)       = plate Sel |- c |+ q
algAttBi (AChc f l r)    = plate AChc |- f |+ l |+ r
algAttBi (Join l r c)    = plate Join |+ l |+ r |- c
algAttBi (Prod l r)      = plate Prod |+ l |+ r
algAttBi (TRef r)        = plate TRef |- r
algAttBi (RenameAlg n q) = plate RenameAlg |- n |+ q
algAttBi Empty           = plate Empty

-- | Biplate of optatt to fexp.
optAttFexpBi :: OptAttribute -> (Str F.FeatureExpr, Str F.FeatureExpr -> OptAttribute)
optAttFexpBi oa@(f,a) = (One f, \(One f) -> oa)


instance Uniplate Algebra where
  uniplate = algUni

instance Biplate Algebra Algebra where
  biplate = plateSelf

instance Uniplate VsqlCond where
  uniplate = vsqlcondUni

instance Biplate VsqlCond F.FeatureExpr where
  biplate = vsqlcondFexpBi

instance Biplate VsqlCond Condition where
  biplate = vsqlcondCondBi

instance Biplate Algebra VsqlCond where
  biplate = algVsqlcondBi

instance Biplate Algebra Condition where
  biplate = algCondBi

instance Biplate OptAttribute F.FeatureExpr where
  biplate = optAttFexpBi 

instance Uniplate OptAttribute where
  uniplate = optAttUni

instance Biplate Algebra OptAttribute where
  biplate = algAttBi

instance Biplate OptAttribute OptAttribute where
  biplate = plateSelf

instance Biplate Algebra F.FeatureExpr where
  biplate = algFexpBi

-- | return the string of alg.
prettyAlg :: Algebra -> String
prettyAlg = P.render . ppAlg

-- | print alg.
ppAlg :: Algebra -> P.Doc
ppAlg (SetOp o l r)   = P.text (ppOp o) 
                     P.$$ P.parens (ppAlg l) 
                     P.$$ P.parens (ppAlg r)
  where
    ppOp Union = "UNION"
    ppOp Diff = "DIFF"
ppAlg (Proj oas q)    = P.text "PROJ" 
                     P.<+> P.braces (ppAtts oas) 
                     P.$$ P.parens (ppAlg q)
  where
    ppQual :: Qualifier -> P.Doc
    ppQual (RelQualifier rn)       = P.text (relationName rn)
    ppQual (SubqueryQualifier qn) = P.text qn
    ppAtts :: OptAttributes -> P.Doc
    ppAtts as = (P.vcat . P.punctuate P.comma . map ppAtt) as
    ppAtt :: OptAttribute -> P.Doc
    ppAtt a 
      | isNothing ((qualifier . getObj) a) 
        = P.text ((attributeName . attribute . getObj) a) 
        P.<> P.brackets (P.text (show (getFexp a)))
      | otherwise 
        = ppQual (fromJust ((qualifier . getObj) a)) 
        P.<> P.char '.' 
        P.<> P.text ((attributeName . attribute . getObj) a) 
        P.<> P.brackets (P.text (show (getFexp a)))
ppAlg (Sel c q)       = P.text "SEL" 
                     P.<+> P.text (show c) 
                     P.$$ P.parens (ppAlg q)
ppAlg (AChc f l r)    = P.text "ACHC" 
                     P.<+> P.brackets (P.text (show f)) 
                     P.$$ P.parens (ppAlg l) 
                     P.$$ P.semi 
                     P.<> P.parens (ppAlg r)
ppAlg (Join l r c)    = P.text "JOIN" 
                     P.<+> P.text (show c)
                     P.$$ P.parens (ppAlg l) 
                     P.$$ P.parens (ppAlg r) 
ppAlg (Prod l r)      = P.text "PROD" 
                     P.$$ P.parens (ppAlg l) 
                     P.$$ P.parens (ppAlg r)
ppAlg (TRef r)        = P.text $ relationName r
ppAlg (RenameAlg n q) = P.text "RENAME" 
                     P.<+> P.text n 
                     P.$$ P.parens (ppAlg q)
ppAlg Empty = P.text "EMPTY"

instance Show Algebra where
  show = prettyAlg

