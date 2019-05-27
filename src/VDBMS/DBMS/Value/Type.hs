-- | Primitive types.
module VDBMS.DBMS.Value.Type (

        SqlType(..)

) where

-- import Prelude hiding (Ordering(..))

import Data.Data (Data,Typeable)
import Data.Text (Text)
import Data.Time.LocalTime (ZonedTime,zonedTimeToUTC)

import Database.HDBC (SqlValue(..))

-- | Primitive types.
data SqlType = TString
             | TByteString 
             | TWord32
             | TWord64
             | TInt32
             | TInt64
             | TInteger
             | TChar
             | TBool
             | TDouble
             | TRational
             | TLocalDate
             | TLocalTimeOfDay
             | TZonedLocalTimeOfDay
             | TLocalTime
             | TZonedTime
             | TUTCTime
             | TDiffTime
             | TPOSIXTime
             | TEpochTime
             | TTimeDiff
             | TNull
  deriving (Data,Eq,Show,Typeable,Ord)

deriving instance Data SqlValue

instance Eq ZonedTime where
  a == b = (zonedTimeToUTC a) == (zonedTimeToUTC b)

instance Ord ZonedTime where 
  compare a b = compare (zonedTimeToUTC a) (zonedTimeToUTC b)

deriving instance Ord SqlValue

{-
-- | Primitive types.
data Type = TInt | TBool | TString
  deriving (Data,Eq,Show,Typeable,Ord)

-- | Primitive values.
data Value
   = I Int
   | B Bool
   | S String
  deriving (Data,Eq,Show,Typeable,Ord)
-}
