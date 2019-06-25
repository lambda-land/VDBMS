-- | Typed symbol domains.
module VDBMS.VDB.Name (

        Attribute(..),
        Relation(..),
        PresCondAtt(..),
        Rename(..),
        QualifiedAttribute(..)

) where

import Data.Data (Data,Typeable)
import Data.String (IsString)


-- | An attribute (i.e. column) name.
newtype Attribute = Attribute { attributeName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | A new name that could be used for attributes and subqueries.
newtype Rename a = Rename {name :: Maybe a}
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | A qualified attribute (i.e., its relation name can be
--   attached to it) with the possibility to rename to a new
--   name.
data QualifiedAttribute = 
  QualifiedAttribute {
    attribute :: Attribute,
    relation :: Maybe Relation
  }
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | A relation (i.e. table) name.
newtype Relation = Relation { relationName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | Name of presence condition attribute in db.
newtype PresCondAtt = PresCondAtt { presCondAttName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)  

