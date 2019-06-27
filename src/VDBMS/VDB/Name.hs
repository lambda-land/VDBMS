-- | Typed symbol domains.
module VDBMS.VDB.Name (

        Attribute(..),
        Relation(..),
        PresCondAtt(..),
        Rename(..),
        QualifiedAttribute(..),
        Attributes(..),
        SingleAttribute(..)

) where

import Data.Data (Data,Typeable)
import Data.String (IsString)


-- | An attribute (i.e. column) name.
newtype Attribute = Attribute { attributeName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | A qualified attribute (i.e., its relation name can be
--   attached to it) with the possibility to rename to a new
--   name.
data QualifiedAttribute = 
    RelationQualifiedAttribute {
      attr :: Attribute, -- ^ the attribute
      rel :: Relation -- ^ the relation 
    }
  | SubqueryQualifiedAttribute {
      attribute :: Attribute, -- ^ the attribute
      subqueryName :: String -- ^ the name assigned to the subquery
    }
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | A single attribute.
data SingleAttribute = SingleAttr Attribute
                     | SingleQualifiedAttr QualifiedAttribute
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | Attributes that can be projected in queries.
data Attributes = AllAtt
                | OneAtt (Rename SingleAttribute)
                | AttrList [Rename SingleAttribute]
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | A new name that could be used for attributes and subqueries.
data Rename a = 
  Rename {
    name :: Maybe String, -- ^ the potentially assigned name
    thing :: a -- ^ the thing
  }
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | A relation (i.e. table) name.
newtype Relation = Relation { relationName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | Name of presence condition attribute in db.
newtype PresCondAtt = PresCondAtt { presCondAttName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)  

