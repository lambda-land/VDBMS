-- | Typed symbol domains.
module VDB.Name where

import Data.Data (Data,Typeable)
import Data.String (IsString)


-- | A feature is a named, boolean configuration option.
newtype Feature = Feature { featureName :: String }
  deriving (Data,Eq,IsString,Ord,Show,Typeable)

-- | An attribute (i.e. column) name.
newtype Attribute = Attribute { attributeName :: String }
  deriving (Data,Eq,IsString,Ord,Show,Typeable)

-- | A relation (i.e. table) name.
newtype Relation = Relation { relationName :: String }
  deriving (Data,Eq,IsString,Ord,Show,Typeable)
