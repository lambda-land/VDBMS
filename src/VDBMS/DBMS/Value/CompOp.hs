  -- | Primitive values and operations.
module VDBMS.DBMS.Value.CompOp (

        CompOp(..),
        prettyCompOp,
        compOp

) where

import Prelude hiding (Ordering(..))

import Data.Data (Data,Typeable)


-- | Comparison operations.
data CompOp = EQ | NEQ | LT | LTE | GTE | GT
  deriving (Data,Eq,Typeable,Ord)

-- | pretty print compOp
prettyCompOp :: CompOp -> String
prettyCompOp EQ  = " = "
prettyCompOp NEQ = " <> "
prettyCompOp LT  = " < "
prettyCompOp LTE = " <= "
prettyCompOp GTE = " >= "
prettyCompOp GT  = " > "

instance Show CompOp where 
  show = prettyCompOp

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
