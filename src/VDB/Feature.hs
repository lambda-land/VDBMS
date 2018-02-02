module VDB.Feature where

import Data.Data (Data,Typeable)
import Data.String (IsString)
import GHC.Generics (Generic)


-- | A feature is a named, boolean configuration option.
newtype Feature = Feature { featureName :: String }
  deriving (Data,Eq,Generic,IsString,Ord,Show,Typeable)
