-- | Typed symbol domains.
module VDBMS.VDB.Name (

        Attribute(..),
        Relation(..),
        PresCondAtt(..)

) where

import Data.Data (Data,Typeable)
import Data.String (IsString)


-- | An attribute (i.e. column) name.
newtype Attribute = Attribute { attributeName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | A relation (i.e. table) name.
newtype Relation = Relation { relationName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | Name of presence condition attribute in db.
newtype PresCondAtt = PresCondAtt { presCondAttName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)  

