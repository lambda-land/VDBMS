-- | Featues.
module VDBMS.Features.Feature (

        Feature,
        featureName

) where

import Data.Data (Data,Typeable)
import Data.String (IsString)

-- | A feature is a named, boolean configuration option.
newtype Feature = Feature { featureName :: String }
  deriving (Data,Eq,IsString,Ord,Show,Typeable)

