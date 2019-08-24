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

-- | SQL conditions, depends on what language
--   you pass it.
data SqlCond a
   = SqlCond RCondition
   | SqlIn   Attr a
   | SqlNot  (SqlCond a)
   | SqlOr   (SqlCond a) (SqlCond a)
   | SqlAnd  (SqlCond a) (SqlCond a)
  deriving (Data,Eq,Typeable,Ord)

-- | pretty prints pure relational conditions.
prettySqlCond :: Show a => SqlCond a -> String
prettySqlCond c = top c
  where
    top (SqlCond r) = show r
    top (SqlOr l r) = sub l ++ " OR " ++ sub r 
    top (SqlAnd l r) = sub l ++ " AND " ++ sub r
    top c = sub c
    sub (SqlIn a q) = attributeName (attribute a) ++ " IN ( " ++ show q ++ " ) "
    sub (SqlNot c) = " NOT " ++ sub c
    sub c = " ( " ++ top c ++ " ) "

instance Show a => Show (SqlCond a) where
  show = prettySqlCond


instance Boolean (SqlCond a) where
  true  = SqlCond (RLit True)
  false = SqlCond (RLit False)
  bnot  = SqlNot
  (&&&) = SqlAnd
  (|||) = SqlOr
