  -- | Primitive values and operations.
module VDB.Type where

import Prelude hiding (Ordering(..))

import Data.Data (Data,Typeable)
-- import Data.Time (ZonedTime)
import Data.Time.LocalTime (ZonedTime,zonedTimeToUTC)

import Database.HDBC
-- import Database.HDBC.ColTypes

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

-- | Comparison operations.
data CompOp = EQ | NEQ | LT | LTE | GTE | GT
  deriving (Data,Eq,Show,Typeable,Ord)

{-
-- | Get the type of a value.
typeOf :: Value -> Type
typeOf (I _) = TInt
typeOf (B _) = TBool
typeOf (S _) = TString
-}

-- | Get the type of a value.
typeOf :: SqlValue -> SqlType
typeOf (SqlString _)                = TString
typeOf (SqlByteString _)            = TByteString
typeOf (SqlWord32 _)                = TWord32
typeOf (SqlWord64 _)                = TWord64
typeOf (SqlInt32 _)                 = TInt32
typeOf (SqlInt64 _)                 = TInt64
typeOf (SqlInteger _)               = TInteger
typeOf (SqlChar _)                  = TChar
typeOf (SqlBool _)                  = TBool
typeOf (SqlDouble _)                = TDouble
typeOf (SqlRational _)              = TRational
typeOf (SqlLocalDate _)             = TLocalDate
typeOf (SqlLocalTimeOfDay _)        = TLocalTimeOfDay
typeOf (SqlZonedLocalTimeOfDay _ _) = TZonedLocalTimeOfDay
typeOf (SqlLocalTime _)             = TLocalTime
typeOf (SqlZonedTime _)             = TZonedTime
typeOf (SqlUTCTime _)               = TUTCTime
typeOf (SqlDiffTime _)              = TDiffTime
typeOf (SqlPOSIXTime _)             = TPOSIXTime
typeOf (SqlEpochTime _)             = TEpochTime
typeOf (SqlTimeDiff _)              = TTimeDiff
typeOf SqlNull                      = TNull
-- typeOf x                            = error "what the hell kind of sqlvalue is this?  " ++ show x


-- | Semantics of a comparison operation.
compOp :: Ord a => CompOp -> a -> a -> Bool
compOp EQ  = (==)
compOp NEQ = (/=)
compOp LT  = (<)
compOp LTE = (<=)
compOp GTE = (>=)
compOp GT  = (>)

{-
-- | Apply a comparison operation to two values. Returns 'Nothing' if the
--   values are not of the same type.
evalCompOp :: CompOp -> Value -> Value -> Maybe Bool
evalCompOp o (I l) (I r) = Just (compOp o l r)
evalCompOp o (B l) (B r) = Just (compOp o l r)
evalCompOp o (S l) (S r) = Just (compOp o l r)
evalCompOp _ _ _ = Nothing
-}

-- | Apply a comparison operation to two values. Returns 'Nothing' if the
--   values are not of the same type.
evalCompOp :: CompOp -> SqlValue -> SqlValue -> Maybe Bool
evalCompOp o (SqlString l)                (SqlString r)                = Just (compOp o l r)
evalCompOp o (SqlByteString l)            (SqlByteString r)            = Just (compOp o l r)
evalCompOp o (SqlWord32 l)                (SqlWord32 r)                = Just (compOp o l r)
evalCompOp o (SqlWord64 l)                (SqlWord64 r)                = Just (compOp o l r)
evalCompOp o (SqlInt32 l)                 (SqlInt32 r)                 = Just (compOp o l r)
evalCompOp o (SqlInt64 l)                 (SqlInt64 r)                 = Just (compOp o l r)
evalCompOp o (SqlInteger l)               (SqlInteger r)               = Just (compOp o l r)
evalCompOp o (SqlChar l)                  (SqlChar r)                  = Just (compOp o l r)
evalCompOp o (SqlBool l)                  (SqlBool r)                  = Just (compOp o l r)
evalCompOp o (SqlDouble l)                (SqlDouble r)                = Just (compOp o l r)
evalCompOp o (SqlRational l)              (SqlRational r)              = Just (compOp o l r)
evalCompOp o (SqlLocalDate l)             (SqlLocalDate r)             = Just (compOp o l r)
evalCompOp o (SqlLocalTimeOfDay l)        (SqlLocalTimeOfDay r)        = Just (compOp o l r)
evalCompOp o (SqlZonedLocalTimeOfDay l x) (SqlZonedLocalTimeOfDay r y) = Just (compOp o l r && compOp o x y)
evalCompOp o (SqlLocalTime l)             (SqlLocalTime r)             = Just (compOp o l r)
evalCompOp o (SqlZonedTime l)             (SqlZonedTime r)             
  | o == EQ = Just (SqlZonedTime l == SqlZonedTime r)
  | otherwise = Just False
evalCompOp o (SqlUTCTime l)               (SqlUTCTime r)               = Just (compOp o l r)
evalCompOp o (SqlDiffTime l)              (SqlDiffTime r)              = Just (compOp o l r)
evalCompOp o (SqlPOSIXTime l)             (SqlPOSIXTime r)             = Just (compOp o l r)
evalCompOp o (SqlEpochTime l)             (SqlEpochTime r)             = Just (compOp o l r)
evalCompOp o (SqlTimeDiff l)              (SqlTimeDiff r)              = Just (compOp o l r)
evalCompOp o SqlNull                      SqlNull                      
  | o == EQ   = Just True
  | otherwise = Just False
evalCompOp _ _ _ = Nothing

hdbcType2SqlType :: SqlTypeId -> String
hdbcType2SqlType SqlIntegerT     = "integer"
hdbcType2SqlType SqlBigIntT      = "bigint"
hdbcType2SqlType SqlDateT        = "date"
hdbcType2SqlType SqlVarCharT     = "text"
hdbcType2SqlType (SqlUnknownT s) = s


{-
[
("id",SqlColDesc {colType = SqlIntegerT, colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing}),
("name",SqlColDesc {colType = SqlVarCharT, colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing}),
("presCond",SqlColDesc {colType = SqlVarCharT, colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing})
]
-}

{-
create table test4 (eid integer primary key asc autoincrement);
create table test1 (name varchar(50) default '');
create table test1 (name varchar(50) not null default '');
create table test2 (name varchar(50) default null);
create table test3 (id bigint primary key default 0, date date, test text);


-->describeTable conn "test1"
[("name",SqlColDesc {colType = SqlUnknownT "varchar(50)", colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing})]
-->describeTable conn "test2"
[("name",SqlColDesc {colType = SqlUnknownT "varchar(50)", colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing})]
-->describeTable conn "test3"
[("id",SqlColDesc {colType = SqlUnknownT "bigint", colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing}),
("date",SqlColDesc {colType = SqlUnknownT "date", colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing}),
("test",SqlColDesc {colType = SqlVarCharT, colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing})]
-->describeTable conn "test4"
[("eid",SqlColDesc {colType = SqlIntegerT, colSize = Nothing, colOctetLength = Nothing, colDecDigits = Nothing, colNullable = Nothing})]
-->
-}


