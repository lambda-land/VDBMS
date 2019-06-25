-- | Relational conditions in relational algebra and queries.
module VDBMS.QueryLang.RelAlg.Relational.Condition (

        RCondition(..),
        Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
import Data.Convertible (safeConvert)
import qualified Data.Text as T (pack,Text)

import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr)
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Variational
import VDBMS.QueryLang.RelAlg.Basics.Atom
-- import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)

import Database.HDBC (SqlValue)

-- | Variational conditions.
data RCondition a
   = RLit  Bool
   | RComp CompOp Atom Atom
   | RNot  (RCondition a)
   | ROr   (RCondition a) (RCondition a)
   | RAnd  (RCondition a) (RCondition a)
   -- | RIn   Attribute RAlgebra
   | RIn   Attribute a
  deriving (Data,Eq,Typeable,Ord)

-- | pretty prints pure relational conditions.
prettyRCondition :: Show a => RCondition a -> String
prettyRCondition c = top c
  where
    top (RComp c l r) = show l ++ show c ++ show r
    top (RAnd l r) = sub l ++ " AND " ++ sub r
    top (ROr l r) = sub l ++ " OR " ++ sub r
    top c = sub c
    sub (RLit b) = if b then " true " else " false "
    sub (RNot c) = " NOT " ++ sub c
    sub (RIn a q) = attributeName a ++ " IN " ++ show q
    sub c = " ( " ++ top c ++ " ) "

instance Show a => Show (RCondition a) where
  show = prettyRCondition


instance Boolean (RCondition a) where
  true  = RLit True
  false = RLit False
  bnot  = RNot
  (&&&) = RAnd
  (|||) = ROr
