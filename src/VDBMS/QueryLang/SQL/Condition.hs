-- | Sql conditions in relational algebra and queries.
module VDBMS.QueryLang.SQL.Condition (

        module VDBMS.QueryLang.RelAlg.Relational.Condition
        , SqlCond(..)
        , Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))

import VDBMS.VDB.Name (Attr(..), Attribute(..))
import VDBMS.QueryLang.RelAlg.Basics.Atom
import VDBMS.QueryLang.RelAlg.Relational.Condition

import Data.Generics.Uniplate.Direct
import Data.Generics.Str

-- | SQL conditions, depends on what language
--   you pass it.
data SqlCond a
   = SqlCond RCondition
   | SqlIn   Attr a
   | SqlNot  (SqlCond a)
   | SqlOr   (SqlCond a) (SqlCond a)
   | SqlAnd  (SqlCond a) (SqlCond a)
  deriving (Data,Eq,Typeable,Ord)

-- | Uniplate for relational condition.
sqlcondUni :: (Uniplate a, Biplate a (SqlCond a), Biplate a RCondition) => SqlCond a -> (Str (SqlCond a), Str (SqlCond a) -> (SqlCond a))
sqlcondUni (SqlCond c)  = plate SqlCond |- c
sqlcondUni (SqlIn at a) = plate SqlIn |- at |+ a
sqlcondUni (SqlNot c)   = plate SqlNot |* c 
sqlcondUni (SqlOr l r)  = plate SqlOr |* l |* r
sqlcondUni (SqlAnd l r) = plate SqlAnd |* l |* r

-- | Biplate for SqlCond to relational condition.
sqlcondRcondBi :: (Uniplate a, Biplate a (SqlCond a), Biplate a RCondition) => SqlCond a -> (Str RCondition, Str RCondition -> SqlCond a)
sqlcondRcondBi (SqlCond c)  = plate SqlCond |* c
sqlcondRcondBi (SqlIn at a) = plate SqlIn |- at |+ a
sqlcondRcondBi (SqlNot c)   = plate SqlNot |+ c 
sqlcondRcondBi (SqlOr l r)  = plate SqlOr |+ l |+ r
sqlcondRcondBi (SqlAnd l r) = plate SqlAnd |+ l |+ r

instance (Uniplate a, Biplate a (SqlCond a), Biplate a RCondition) => Uniplate (SqlCond a) where
  uniplate = sqlcondUni

instance (Uniplate a, Biplate a (SqlCond a)) => Biplate (SqlCond a) (SqlCond a) where
  biplate = plateSelf

instance (Uniplate a, Biplate a (SqlCond a), Biplate a RCondition) => Biplate (SqlCond a) RCondition where
  biplate = sqlcondRcondBi

-- | pretty prints pure relational conditions.
prettySqlCond :: Show a => SqlCond a -> String
prettySqlCond c = top c
  where
    top (SqlCond r) = show r
    top (SqlOr l r) = sub l ++ " OR " ++ sub r 
    top (SqlAnd l r) = sub l ++ " AND " ++ sub r
    top c' = sub c'
    sub (SqlIn a q) = attributeName (attribute a) ++ " IN ( " ++ show q ++ " ) "
    sub (SqlNot c') = " NOT " ++ sub c'
    sub c' = " ( " ++ top c' ++ " ) "

instance Show a => Show (SqlCond a) where
  show = prettySqlCond


instance Boolean (SqlCond a) where
  true  = SqlCond (RLit True)
  false = SqlCond (RLit False)
  bnot  = SqlNot
  (&&&) = SqlAnd
  (|||) = SqlOr
