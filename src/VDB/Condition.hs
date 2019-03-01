-- | Variational conditions in relational algebra and queries.
module VDB.Condition where

import Data.Data (Data,Typeable)
import Data.SBV (Boolean(..))
import Data.Convertible (safeConvert)
import qualified Data.Text as T (pack,Text)

import VDB.FeatureExpr (FeatureExpr)
import VDB.Name
import VDB.Type
import VDB.Variational

import Database.HDBC (SqlValue)

-- | Atoms are the leaves of a condition.
data Atom
   = Val  SqlValue
   | Attr Attribute
  deriving (Data,Eq,Typeable,Ord)

-- | pretty print atoms.
prettyAtom :: Atom -> String
prettyAtom (Val v)  = case safeConvert v of 
  Right val -> val
  _ -> error "safeConvert resulted in error!!! showAtom"
prettyAtom (Attr a) = getAttName a
  -- case attributeQualifier a of 
  -- Just r  -> T.concat[T.pack $ relationName r, ".", T.pack $ attributeName a]
  -- Nothing -> T.pack $ attributeName a 

instance Show Atom where
  show = prettyAtom

-- | Variational conditions.
data Condition
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc FeatureExpr Condition Condition
  deriving (Data,Eq,Show,Typeable,Ord)

-- | pretty print conditions
-- prettyCondition :: Condition -> String
-- prettyCondition = undefined

-- instance Show Condition where
--   show = prettyCondition

instance Variational Condition where

  choice = CChc

  choiceMap g (Not c)      = Not (choiceMap g c)
  choiceMap g (Or  l r)    = Or  (choiceMap g l) (choiceMap g r)
  choiceMap g (And l r)    = And (choiceMap g l) (choiceMap g r)
  choiceMap g (CChc f l r) = g f l r
  choiceMap _ c            = c

instance Boolean Condition where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or
