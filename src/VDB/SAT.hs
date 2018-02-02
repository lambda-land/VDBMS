{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | A simple SAT solving interface.
--
--   TODO: need interface for incremental SAT (see: Data.SBV.Control)
module VDB.SAT where

import Control.Monad (liftM2)
import Data.SBV (Boolean(..),SBool,Symbolic,isSatisfiable)
import System.IO.Unsafe (unsafePerformIO)


-- | A type class for types that can be converted to symbolic predicates
--   and checked by a SAT solver.
class Boolean b => SAT b where
  toSymbolic :: b -> Symbolic SBool

-- | Is the predicate satisfiable?
sat :: SAT b => b -> Bool
sat p = unsafePerformIO (isSatisfiable (toSymbolic p))

-- | Is the predicate unsatisfiable?
unsat :: SAT b => b -> Bool
unsat = not . sat

-- | Is the predicate a tautology?
taut :: SAT b => b -> Bool
taut = unsat . bnot

-- | Are these predicates equivalent?
equiv :: SAT b => b -> b -> Bool
equiv a b = taut (a <=> b)


-- Instances

instance Boolean b => Boolean (Symbolic b) where
  true  = return true
  false = return false
  bnot  = fmap bnot
  (&&&) = liftM2 (&&&)
  (|||) = liftM2 (|||)

instance SAT SBool where
  toSymbolic = return

instance SAT (Symbolic SBool) where
  toSymbolic = id

instance SAT (Symbolic Bool) where
  toSymbolic = fmap fromBool
