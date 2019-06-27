-- | Relational set operations.
module VDBMS.QueryLang.RelAlg.Basics.SetOp (

        SetOp(..)

) where

import Data.Data (Data,Typeable)


-- | Basic set operations.
data SetOp = Union | Diff 
  deriving (Data,Eq,Show,Typeable, Ord)

