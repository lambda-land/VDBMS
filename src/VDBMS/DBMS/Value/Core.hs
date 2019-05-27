  -- | type of sql values.
module VDBMS.DBMS.Value.Core (

        typeOf,
        hdbcType2SqlType

) where

import VDBMS.DBMS.Value.Type

import Database.HDBC (SqlValue(..), SqlTypeId(..))


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

hdbcType2SqlType :: SqlTypeId -> String
hdbcType2SqlType SqlIntegerT     = "integer"
hdbcType2SqlType SqlBigIntT      = "bigint"
hdbcType2SqlType SqlDateT        = "date"
hdbcType2SqlType SqlVarCharT     = "text"
hdbcType2SqlType (SqlUnknownT s) = s
hdbcType2SqlType _ = error "cannot convert hdbc type to sql type!!"


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


