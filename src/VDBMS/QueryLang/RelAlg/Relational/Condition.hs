-- | Relational conditions in relational algebra and queries.
module VDBMS.QueryLang.RelAlg.Relational.Condition (

        RCondition(..)
        , Atom(..)
        , CompOp(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
-- import Data.Convertible (safeConvert)
-- import qualified Data.Text as T (pack,Text)

-- import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
-- import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value
-- import VDBMS.Variational.Variational
import VDBMS.QueryLang.RelAlg.Basics.Atom

-- import Database.HDBC (SqlValue)

import Data.Generics.Uniplate.Direct
import Data.Generics.Str

-- Pure relational conditions.
data RCondition
   = RLit  Bool
   | RComp CompOp Atom Atom
   | RNot  RCondition
   | ROr   RCondition RCondition 
   | RAnd  RCondition RCondition 
  deriving (Data,Eq,Typeable,Ord)

-- | Uniplate for relational condition.
rcondUni :: RCondition -> (Str RCondition, Str RCondition -> RCondition)
rcondUni (RLit b)      = plate RLit |- b
rcondUni (RComp o l r) = plate RComp |- o |- l |- r
rcondUni (RNot c)      = plate RNot |* c 
rcondUni (ROr l r)     = plate ROr |* l |* r
rcondUni (RAnd l r)    = plate RAnd |* l |* r

instance Uniplate RCondition where
  uniplate = rcondUni

instance Biplate RCondition RCondition where
  biplate = plateSelf

-- | pretty prints pure relational conditions.
prettyRCondition :: RCondition -> String
prettyRCondition c = top c
  where
    top (RComp o l r) = show l ++ show o ++ show r
    top (RAnd l r) = sub l ++ " AND " ++ sub r
    top (ROr l r) = sub l ++ " OR " ++ sub r
    top c' = sub c'
    sub (RLit b) = if b then " true " else " false "
    sub (RNot c') = " NOT " ++ sub c'
    sub c' = " ( " ++ top c' ++ " ) "

instance Show RCondition where
  show = prettyRCondition

instance Boolean RCondition where
  true  = RLit True
  false = RLit False
  bnot  = RNot
  (&&&) = RAnd
  (|||) = ROr
