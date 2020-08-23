-- | Relational algebra.
module VDBMS.QueryLang.RelAlg.Relational.Algebra (

        RAlgebra(..)
        , SetOp(..)
        , module VDBMS.QueryLang.SQL.Condition

) where

import Data.Data (Data,Typeable)

import VDBMS.VDB.Name
import VDBMS.QueryLang.SQL.Condition
import VDBMS.QueryLang.RelAlg.Basics.SetOp

import Data.Generics.Uniplate.Direct
import Data.Generics.Str

import Prelude hiding ((<>), concat)
import Text.PrettyPrint
import Data.Maybe (isNothing, fromJust)

-- | More expressive relaitonal algebra.
--   Ie, it has renaming of attributes and subqueries in addition to 
--   qualified attributes.
data RAlgebra
   = RSetOp SetOp RAlgebra RAlgebra
   | RProj  Attributes RAlgebra
   | RSel   (SqlCond RAlgebra) RAlgebra
   | RJoin RAlgebra RAlgebra RCondition
   | RProd RAlgebra RAlgebra
   | RTRef  Relation
   | RRenameAlg Name RAlgebra
   | REmpty
  deriving (Data,Eq,Typeable,Ord)

-- | Uniplate for relational algebra.
ralgUni :: RAlgebra -> (Str RAlgebra, Str RAlgebra -> RAlgebra)
ralgUni (RSetOp o l r)   = plate RSetOp |- o |* l |* r
ralgUni (RProj as q)     = plate RProj |- as |* q
ralgUni (RSel c q)       = plate RSel |- c |* q 
ralgUni (RJoin l r c)    = plate RJoin |* l |* r |- c 
ralgUni (RProd l r)      = plate RProd |* l |* r 
ralgUni (RTRef r)        = plate RTRef |- r
ralgUni (RRenameAlg n q) = plate RRenameAlg |- n |* q
ralgUni REmpty           = (Zero, \Zero -> REmpty)

-- | Biplate for relational alg to relational cond.
ralgRcondBi :: RAlgebra -> (Str RCondition, Str RCondition -> RAlgebra)
ralgRcondBi (RSetOp o l r)   = plate RSetOp |- o |+ l |+ r
ralgRcondBi (RProj as q)     = plate RProj |- as |+ q
ralgRcondBi (RSel c q)       = plate RSel |+ c |+ q 
ralgRcondBi (RJoin l r c)    = plate RJoin |+ l |+ r |* c 
ralgRcondBi (RProd l r)      = plate RProd |+ l |+ r 
ralgRcondBi (RTRef r)        = plate RTRef |- r
ralgRcondBi (RRenameAlg n q) = plate RRenameAlg |- n |+ q
ralgRcondBi REmpty           = (Zero, \Zero -> REmpty)

-- | Biplate for raltional alg to slqcond.
ralgSqlcondBi :: RAlgebra -> (Str (SqlCond RAlgebra), Str (SqlCond RAlgebra) -> RAlgebra)
ralgSqlcondBi (RSetOp o l r)   = plate RSetOp |- o |+ l |+ r
ralgSqlcondBi (RProj as q)     = plate RProj |- as |+ q
ralgSqlcondBi (RSel c q)       = plate RSel |* c |+ q 
ralgSqlcondBi (RJoin l r c)    = plate RJoin |+ l |+ r |- c 
ralgSqlcondBi (RProd l r)      = plate RProd |+ l |+ r 
ralgSqlcondBi (RTRef r)        = plate RTRef |- r
ralgSqlcondBi (RRenameAlg n q) = plate RRenameAlg |- n |+ q
ralgSqlcondBi REmpty           = (Zero, \Zero -> REmpty)

instance Uniplate RAlgebra where
  uniplate = ralgUni

instance Biplate RAlgebra RAlgebra where
  biplate = plateSelf

instance Biplate RAlgebra RCondition where
  biplate = ralgRcondBi

instance Biplate RAlgebra (SqlCond RAlgebra) where
  biplate = ralgSqlcondBi

-- | return the string of relational alg.
prettyRAlg :: RAlgebra -> String 
prettyRAlg = render . ppRAlg

-- | print relational alg.
ppRAlg :: RAlgebra -> Doc 
ppRAlg (RSetOp o l r)   = text (ppROP o)
                       $$ parens (ppRAlg l)
                       $$ parens (ppRAlg r)
  where
    ppROP Union = "UNION"
    ppROP Diff = "DIFF"
ppRAlg (RProj as q)     = text "PROJ"
                       <+> braces (ppRAtts as)
                       $$ parens (ppRAlg q)
  where
    ppQual :: Qualifier -> Doc
    ppQual (RelQualifier rn)      = text (relationName rn)
    ppQual (SubqueryQualifier qn) = text qn
    ppRAtts :: Attributes -> Doc
    ppRAtts = vcat . punctuate comma . map ppRAtt
    ppRAtt :: Attr -> Doc
    ppRAtt a 
      | isNothing (qualifier a) = text $ (attributeName . attribute) a
      | otherwise = ppQual (fromJust (qualifier a)) 
                 <> char '.' 
                 <> text ((attributeName . attribute) a) 
ppRAlg (RSel c q)       = text "SEL"
                       <+> text (show c)
                       $$ parens (ppRAlg q)
ppRAlg (RJoin l r c)    = text "JOIN"
                       <+> text (show c)
                       $$ parens (ppRAlg l)
                       $$ parens (ppRAlg r)
ppRAlg (RProd l r)      = text "PROD"
                       $$ parens (ppRAlg l)
                       $$ parens (ppRAlg r)
ppRAlg (RTRef r)        = text $ relationName r
ppRAlg (RRenameAlg n q) = text "RENAME"
                       <+> text n
                       $$ parens (ppRAlg q)
ppRAlg REmpty           = text "EMPTY"

instance Show RAlgebra where
  show = prettyRAlg