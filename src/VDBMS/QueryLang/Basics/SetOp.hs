-- | Relational set operations.
module VDBMS.QueryLang.Basics.SetOp (

        SetOp(..)

) where

import Data.Data (Data,Typeable)


-- | Basic set operations.
data SetOp = Union | Diff | Prod
  deriving (Data,Eq,Show,Typeable, Ord)
