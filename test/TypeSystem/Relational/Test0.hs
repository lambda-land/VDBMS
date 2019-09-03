module TypeSystem.Relational.Test0 where

import VDB.Schema.Relational.Sample

import VDBMS.TypeSystem.Relational.TypeSystem 
import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Name
import VDBMS.VDB.GenName
import VDBMS.DBMS.Value.Type

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Catch
import Control.Monad.IO.Class
-- import Control.Exception
import Control.Monad (guard)

import Data.Map




-- | test relational type system.
trtypesys :: TestTree
trtypesys = testGroup "Relational Type System Tests" [uts]

-- | Unit tests.
uts :: TestTree
uts = testGroup "Unit tests" [t1, t2, t3, t4, t5]

q0, q1 :: RAlgebra

-- 
-- set operation
-- 

-- 
-- projection
-- 

-- 
-- selection
-- 

-- t6 :: TestTree
-- t6 = testCase "query: σ (A = 2) R" $
--   do let expectVal = fromList [(a, [RAttrInfo TInt32 (RelQualifier r)])]
--      output <- typeOfRQuery (RSel ) sampleRSch 
--      output @?= expectVal

-- 
-- join
-- 

-- 
-- production
-- 

-- 
-- relation reference 
-- 

t5 :: TestTree
t5 = testCase "query: RR = R" $ 
  utest q1 sampleRSch (fromList [(a, [RAttrInfo TInt32 (relQual "RR")])])

q1 = RTRef (rename "RR" r)

t4 :: TestTree
t4 = testCase "query: R" $ 
  utest q0 sampleRSch (fromList [(a, [RAttrInfo TInt32 (RelQualifier r)])])

q0 = RTRef (Rename Nothing r) 

t3 :: TestTree
t3 = testCase "refer missing relation w rename" $
  excpTest (RTRef (rename "R" miss)) sampleRSch (RMissingRelation miss) 

t2 :: TestTree
t2 = testCase "refer missing relation" $
  excpTest (RTRef (Rename Nothing miss)) sampleRSch (RMissingRelation miss)

-- 
-- empty 
-- 
t1 :: TestTree
t1 = testCase "query: ⊥ " $ utest REmpty sampleRSch empty
  -- liftIO $ putStrLn (show output)

-- | unit test for relational type system without exceptions.
utest :: RAlgebra -> RSchema -> RTypeEnv -> Assertion 
utest q s t = 
  do output <- typeOfRQuery q s 
     output @?= t

-- | unit test for relational type system for exceptions.
excpTest :: RAlgebra -> RSchema -> RSchemaError -> IO ()
excpTest q s err = assertException err (typeOfRQuery q s)

-- | checks the exceptions.
assertException :: (Exception e, Eq e) => e -> IO a -> IO ()
assertException ex action =
    handleJust isWanted (const $ return ()) $ do
        action
        assertFailure $ "Expected exception: " ++ show ex
  where isWanted = guard . (== ex)

-- testPasses = TestCase $ assertException DivideByZero (evaluate $ 5 `div` 0)
-- testFails  = TestCase $ assertException DivideByZero (evaluate $ 5 `div` 1)

