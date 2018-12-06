  -- | Primitive values and operations.
module VDB.Type where

import Prelude hiding (Ordering(..))

import Data.Data (Data,Typeable)

import Database.HDBC

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

-- | Primitive values.
-- data Value
--    = I Int
--    | B Bool
--    | S String
--   deriving (Data,Eq,Show,Typeable,Ord)

-- | Comparison operations.
-- data CompOp = EQ | NEQ | LT | LTE | GTE | GT
  -- deriving (Data,Eq,Show,Typeable,Ord)

-- | Get the type of a value.
typeOf :: SqlValue -> SqlType
typeOf (SqlString _)                = TString
typeOf (SqlByteString _)            = TByteString
typeOf (SqlWord32 _)                = TWord32
typeOf (SqlWord64 _)                = TWord64
typeof (SqlInt32 _)                 = TInt32
typeof (SqlInt64 _)                 = TInt64
typeof (SqlInteger _)               = TInteger
typeof (SqlChar _)                  = TChar
typeof (SqlBool _)                  = TBool
typeof (SqlDouble _)                = TDouble
typeof (SqlRational _)              = TRational
typeof (SqlLocalDate _)             = TLocalDate
typeof (SqlLocalTimeOfDay _)        = TLocalTimeOfDay
typeof (SqlZonedLocalTimeOfDay _ _) = TZonedLocalTimeOfDay
typeof (SqlLocalTime _)             = TLocalTime
typeof (SqlZonedTime _)             = TZonedTime
typeof (SqlUTCTime _)               = TUTCTime
typeof (SqlDiffTime _)              = TDiffTime
typeof (SqlPOSIXTime _)             = TPOSIXTime
typeof (SqlEpochTime _)             = TEpochTime
typeof (SqlTimeDiff _)              = TTimeDiff
typeof SqlNull                      = TNull

-- | Semantics of a comparison operation.
-- compOp :: Ord a => CompOp -> a -> a -> Bool
-- compOp EQ  = (==)
-- compOp NEQ = (/=)
-- compOp LT  = (<)
-- compOp LTE = (<=)
-- compOp GTE = (>=)
-- compOp GT  = (>)

-- | Apply a comparison operation to two values. Returns 'Nothing' if the
--   values are not of the same type.
-- evalCompOp :: CompOp -> Value -> Value -> Maybe Bool
-- evalCompOp o (I l) (I r) = Just (compOp o l r)
-- evalCompOp o (B l) (B r) = Just (compOp o l r)
-- evalCompOp o (S l) (S r) = Just (compOp o l r)
-- evalCompOp _ _ _ = Nothing
