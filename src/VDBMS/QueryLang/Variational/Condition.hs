-- | Variational conditions in variational algebra and queries.
module VDBMS.QueryLang.Variational.Condition (

        Condition(..),
        Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
-- import Data.Convertible (safeConvert)
-- import qualified Data.Text as T (pack,Text)

import VDBMS.Features.FeatureExpr.FeatureExpr (FeatureExpr, evalFeatureExpr)
-- import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Variational
import VDBMS.QueryLang.Basics.Atom
import VDBMS.QueryLang.Relational.Condition

import Database.HDBC (SqlValue)


-- | Variational conditions.
data Condition
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc FeatureExpr Condition Condition
  deriving (Data,Eq,Typeable,Ord)

-- | pretty prints pure relational conditions.
prettyRelCondition :: Condition -> String
prettyRelCondition (CChc _ _ _) = error "cannot pretty print a choice of conditions!!"
prettyRelCondition c = top c
  where
    top (Comp c l r) = show l ++ show c ++ show r
    top (And l r) = sub l ++ " AND " ++ sub r
    top (Or l r) = sub l ++ " OR " ++ sub r
    top c = sub c
    sub (Lit b) = if b then " true " else " false "
    sub (Not c) = " NOT " ++ sub c
    sub c = " ( " ++ top c ++ " ) "

instance Show Condition where
  show = prettyRelCondition

instance Variational Condition where

  type NonVariational Condition = RCondition
  -- type Configr Condition = Config Bool 
  
  configure c (Lit b)      = RLit b
  configure c (Comp o l r) = RComp o l r
  configure c (Not cond)   = RNot $ configure c cond
  configure c (Or l r)     = ROr (configure c l) (configure c r)
  configure c (And l r)    = RAnd (configure c l) (configure c r)
  configure c (CChc f l r) 
    | evalFeatureExpr c f  = configure c l
    | otherwise            = configure c r
  -- configure c cond         = cond

  -- choice = CChc

  -- choiceMap g (Not c)      = Not (choiceMap g c)
  -- choiceMap g (Or  l r)    = Or  (choiceMap g l) (choiceMap g r)
  -- choiceMap g (And l r)    = And (choiceMap g l) (choiceMap g r)
  -- choiceMap g (CChc f l r) = g f l r
  -- choiceMap _ c            = c

instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or
