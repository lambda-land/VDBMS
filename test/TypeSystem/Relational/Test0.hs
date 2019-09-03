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

import Prelude hiding (Ordering(..))
import Data.Map

import Database.HDBC (iToSql)


-- | test relational type system.
trtypesys :: TestTree
trtypesys = testGroup "Relational Type System Tests" [uts]

-- | Unit tests.
uts :: TestTree
uts = testGroup "Unit tests" [t1, t2, t3, t4, t5, t6, t7]

q0, q1, q2 :: RAlgebra
rq2 :: Rename RAlgebra

-- 
-- set operation
-- 

-- 
-- projection
-- 

-- 
-- selection
-- 

t6 :: TestTree
t6 = testCase "query: σ (true) R" $
  utest q2 sampleRSch (fromList [(a, [RAttrInfo TInt64 (RelQualifier r)])]) 

q2 = RSel 
  (SqlCond (RLit True))
  rq2

rq2 = (Rename Nothing q0)

t7 :: TestTree
t7 = testCase "query: σ (A = 2) R" $
  utest q3 sampleRSch (fromList [(a, [RAttrInfo TInt64 (RelQualifier r)])]) 

q3 = RSel c1 rq2

c1 = SqlCond (RComp EQ (Att (Attr a Nothing))
                       (Val (iToSql 2)))
c2 = SqlCond (RComp EQ (Att (Attr a (Just (RelQualifier r))))
                       (Val (iToSql 2)))
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
  utest q1 sampleRSch (fromList [(a, [RAttrInfo TInt64 (relQual "RR")])])

q1 = RTRef (rename "RR" r)

t4 :: TestTree
t4 = testCase "query: R" $ 
  utest q0 sampleRSch (fromList [(a, [RAttrInfo TInt64 (RelQualifier r)])])

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

