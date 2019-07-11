-- | Typed symbol domains.
module VDBMS.VDB.Name (

        Attribute(..),
        Relation(..),
        PresCondAtt(..),
        Rename(..),
        Qualifier(..),
        Attr(..),
        Attributes(..),
        renameMap,
        attsSet

) where

import Data.Data (Data,Typeable)
import Data.String (IsString)

import Data.Set (Set)
import qualified Data.Set as Set (fromList)

-- | An attribute (i.e. column) name.
newtype Attribute = Attribute { attributeName :: String }
  deriving (Data,Eq,IsString,Ord,Read,Show,Typeable)

-- | Qualifiers for attributes.
data Qualifier 
  = RelQualifier {
      relQualifier :: Relation
    }
  | SubqueryQualifier {
      subqueryQualifier :: String
    }
 deriving (Data,Eq,Ord,Read,Show,Typeable)

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

-- | A new name that could be used for attributes and subqueries.
data Rename a = 
  Rename {
    name  :: Maybe String, -- ^ the potentially assigned name
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

