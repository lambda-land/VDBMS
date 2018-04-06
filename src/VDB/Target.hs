module VDB.Target where

import VDB.Condition (Atom(..))
import VDB.FeatureExpr (FeatureExpr)
import VDB.Name
import VDB.Value


-- | Variational conditions.
data Condition
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | SAT  FeatureExpr  -- TODO: if all SAT problems have similar structure,
                       -- make this more specific (e.g. two FeatureExpr args)
  deriving (Data,Eq,Show,Typeable)

-- | Query expression. SELECT ... FROM ... WHERE ...
data Query = Select [Attr] FromExpr (Maybe Condition)
  deriving (Eq,Show)

-- | TODO: Add Join.
type FromExpr = [Relation]


