-- | Typed symbol domains.
module VDBMS.VDB.Name (

        Attribute(..)
        , Relation(..)
        , presCondAttName
        , PCatt
        , Name
        , Rename(..)
        , Alias
        , Qualifier(..)
        , Attr(..)
        , Attributes
        , renameMap
        , attsSet
        , qualName

) where

import Data.Data (Data,Typeable)
import Data.String (IsString)

import Data.Set (Set)
import qualified Data.Set as Set (fromList)

-- | Names.
type Name = String

-- | An attribute (i.e. column) name.
newtype Attribute = Attribute { attributeName :: Name }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | Qualifiers for attributes.
data Qualifier 
  = RelQualifier {
      relQualifier :: Relation
    }
  | SubqueryQualifier {
      subqueryQualifier :: Name
    }
 deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | The qualifier name.
qualName :: Qualifier -> String
qualName (RelQualifier r) = relationName r 
qualName (SubqueryQualifier q) = q 

-- | A qualified/unqualified attribute (i.e., its relation name can be
--   attached to it) with the possibility to rename to a new
--   name.
data Attr = Attr {
  attribute :: Attribute,
  qualifier :: Maybe Qualifier
}
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | Attributes that can be projected in queries.
type Attributes = [Rename Attr]

-- | Gets a set of attributes.
attsSet :: Attributes -> Set Attribute
attsSet = Set.fromList . fmap (attribute . thing) 

-- | Possible names used for aliasing.
type Alias = Maybe Name

-- | A new name that could be used for attributes and subqueries.
data Rename a = 
  Rename {
    name  :: Alias, -- ^ the potentially assigned name
    thing :: a -- ^ the thing
  }
  deriving (Data,Eq,Ord,Read,Show,Typeable)

-- | Maps a function to objects with renaming.
renameMap :: (a -> b) -> Rename a -> Rename b
renameMap f (Rename n t) = Rename n (f t)

-- | A relation (i.e. table) name.
newtype Relation = Relation { relationName :: Name }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | Name of presence condition attribute in db.
-- newtype PresCondAtt = PresCondAtt { presCondAttName :: Name }
--   deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)  

-- | presence condition attribute.
type PCatt = Attribute

-- | presence condition attribute name.
presCondAttName :: PCatt -> Name 
presCondAttName (Attribute p) = p