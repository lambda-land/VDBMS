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
  deriving (Data,Eq,Show,Typeable,Ord)

-- | print atoms.
showAtom :: Atom -> T.Text
showAtom (Val v)  = case safeConvert v of 
  Right val -> T.pack val
  _ -> error "safeConvert resulted in error!!! showAtom"
showAtom (Attr a) = getAttName a
  -- case attributeQualifier a of 
  -- Just r  -> T.concat[T.pack $ relationName r, ".", T.pack $ attributeName a]
  -- Nothing -> T.pack $ attributeName a 


-- | Variational conditions.
data Condition
   = Lit  Bool
   | Comp CompOp Atom Atom
   | Not  Condition
   | Or   Condition Condition
   | And  Condition Condition
   | CChc FeatureExpr Condition Condition
  deriving (Data,Eq,Show,Typeable,Ord)

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
