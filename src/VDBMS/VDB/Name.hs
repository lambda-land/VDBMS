-- | Typed symbol domains.
module VDBMS.VDB.Name (

        Attribute(..),
        Relation(..),
        PresCondAtt(..),
        Rename(..),
        QualifiedAttr(..),
        Attributes(..),
        SingleAttr(..),
        renameMap

) where

import Data.Data (Data,Typeable)
import Data.String (IsString)


-- | An attribute (i.e. column) name.
newtype Attribute = Attribute { attributeName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | A qualified attribute (i.e., its relation name can be
--   attached to it) with the possibility to rename to a new
--   name.
data QualifiedAttr 
   = RelationQualifiedAttr {
      attr :: Attribute, -- ^ the attribute
      rel :: Relation -- ^ the relation 
     }
   | SubqueryQualifiedAttr {
      attribute :: Attribute, -- ^ the attribute
      subqueryName :: String -- ^ the name assigned to the subquery
     }
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | A single attribute.
data SingleAttr = SingleAttr Attribute
                | SingleQualifiedAttr QualifiedAttr
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | Attributes that can be projected in queries.
type Attributes = [Rename SingleAttr]

-- | A new name that could be used for attributes and subqueries.
data Rename a = 
  Rename {
    name :: Maybe String, -- ^ the potentially assigned name
    thing :: a -- ^ the thing
  }
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | Maps a function to objects with renaming.
renameMap :: (a -> b) -> Rename a -> Rename b
renameMap f (Rename n t) = Rename n (f t)

-- | A relation (i.e. table) name.
newtype Relation = Relation { relationName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | Name of presence condition attribute in db.
newtype PresCondAtt = PresCondAtt { presCondAttName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)  

