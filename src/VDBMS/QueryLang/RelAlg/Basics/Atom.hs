-- | Atoms.
module VDBMS.QueryLang.RelAlg.Basics.Atom (

        Atom(..)

) where

import Data.Data (Data,Typeable)
import Data.Convertible (safeConvert)

import VDBMS.VDB.Name (attributeName, Attribute, QualifiedAttribute)
import VDBMS.DBMS.Value.Value


import Database.HDBC (SqlValue)

-- | Atoms are the leaves of a condition.
data Atom
   = Val  SqlValue
   | Attr Attribute
   | Attr' QualifiedAttribute
  deriving (Data,Eq,Typeable,Ord)

-- data AtomError = UnsafeConversion Atom
-- add error from safeconvert too!
--   deriving (Data,Eq,Generic,Ord,Show,Typeable)


-- | pretty print atoms.
prettyAtom :: Atom -> String
prettyAtom (Val v)  =  case safeConvert v of 
  Right val -> val
  _ -> error "safeConvert resulted in error!!! showAtom"
prettyAtom (Attr a) = attributeName a

instance Show Atom where
  show = prettyAtom
