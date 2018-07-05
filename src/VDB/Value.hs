-- | Primitive values and operations.
module VDB.Value where

import Prelude hiding (Ordering(..))

import Data.Data (Data,Typeable)


-- | Primitive types.
data Type = TInt | TBool | TString
  deriving (Data,Eq,Show,Typeable,Ord)

-- | Primitive values.
data Value
   = I Int
   | B Bool
   | S String
  deriving (Data,Eq,Show,Typeable,Ord)

-- | Comparison operations.
data CompOp = EQ | NEQ | LT | LTE | GTE | GT
  deriving (Data,Eq,Show,Typeable,Ord)

-- | Get the type of a value.
typeOf :: Value -> Type
typeOf (I _) = TInt
typeOf (B _) = TBool
typeOf (S _) = TString

-- | Semantics of a comparison operation.
compOp :: Ord a => CompOp -> a -> a -> Bool
compOp EQ  = (==)
compOp NEQ = (/=)
compOp LT  = (<)
compOp LTE = (<=)
compOp GTE = (>=)
compOp GT  = (>)

-- | Apply a comparison operation to two values. Returns 'Nothing' if the
--   values are not of the same type.
evalCompOp :: CompOp -> Value -> Value -> Maybe Bool
evalCompOp o (I l) (I r) = Just (compOp o l r)
evalCompOp o (B l) (B r) = Just (compOp o l r)
evalCompOp o (S l) (S r) = Just (compOp o l r)
evalCompOp _ _ _ = Nothing
