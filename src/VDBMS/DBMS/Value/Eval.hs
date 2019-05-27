  -- | Evaluation of operations.
module VDBMS.DBMS.Value.Eval (

        evalCompOp

) where

import VDBMS.DBMS.Value.CompOp

-- import Prelude hiding (EQ)
import Prelude hiding (Ordering(..))

import Database.HDBC (SqlValue(..))

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

