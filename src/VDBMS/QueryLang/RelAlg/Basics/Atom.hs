-- | Atoms.
module VDBMS.QueryLang.RelAlg.Basics.Atom (

        Atom(..)
        -- , prettyAttr

) where

import Data.Data (Data,Typeable)
import Data.Convertible (safeConvert)
import Data.Maybe (fromJust, isNothing)

import VDBMS.VDB.Name (attributeName, Attr(..), qualName)
import VDBMS.DBMS.Value.Value ()


import Database.HDBC (SqlValue)

-- | Atoms are the leaves of a condition.
data Atom
   = Val  SqlValue
   | Att Attr
  deriving (Data,Eq,Typeable,Ord)

-- data AtomError = UnsafeConversion Atom
-- add error from safeconvert too!
--   deriving (Data,Eq,Generic,Ord,Show,Typeable)


-- | pretty print atoms.
prettyAtom :: Atom -> String
prettyAtom (Val v)  =  case safeConvert v of 
  Right val -> val
  _ -> error "safeConvert resulted in error!!! showAtom"
prettyAtom (Att a) = prettyAttr a

-- | pretty prints an attribute.
prettyAttr :: Attr -> String
prettyAttr a 
  | isNothing q = attributeName $ attribute a 
  | otherwise = ((qualName . fromJust) q) ++ "." ++ attributeName (attribute a)
    where
      q = qualifier a

instance Show Atom where
  show = prettyAtom
