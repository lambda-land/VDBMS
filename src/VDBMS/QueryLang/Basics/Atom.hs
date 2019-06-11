-- | Atoms.
module VDBMS.QueryLang.Basics.Atom (

        Atom(..)

) where

import Data.Data (Data,Typeable)
-- import GHC.Generics (Generic)
-- import Data.SBV (Boolean(..))
import Data.Convertible (safeConvert)
-- import qualified Data.Text as T (pack,Text)
-- import Control.Monad.Catch (MonadThrow)
-- import Control.Monad.Either (runEitherT)

import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value


import Database.HDBC (SqlValue)

-- | Atoms are the leaves of a condition.
data Atom
   = Val  SqlValue
   | Attr Attribute
  deriving (Data,Eq,Typeable,Ord)

-- data AtomError = UnsafeConversion Atom
--   deriving (Data,Eq,Generic,Ord,Show,Typeable)


-- | pretty print atoms.
prettyAtom :: Atom -> String
prettyAtom (Val v)  =  case safeConvert v of 
  Right val -> val
  _ -> error "safeConvert resulted in error!!! showAtom"
prettyAtom (Attr a) = getAttName a
  -- case attributeQualifier a of 
  -- Just r  -> T.concat[T.pack $ relationName r, ".", T.pack $ attributeName a]
  -- Nothing -> T.pack $ attributeName a 

instance Show Atom where
  show = prettyAtom
