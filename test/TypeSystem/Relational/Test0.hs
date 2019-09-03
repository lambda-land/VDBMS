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
-- t6 = testCase "query "

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
  do let expectVal = fromList [(a, [RAttrInfo TInt32 (relQual "RR")])]
     output <- typeOfRQuery (RTRef (rename "RR" r)) sampleRSch
     output @?= expectVal


t4 :: TestTree
t4 = testCase "query: R" $
  do let expectVal = fromList [(a, [RAttrInfo TInt32 (RelQualifier r)])]
     output <- typeOfRQuery (RTRef (Rename Nothing r)) sampleRSch
     output @?= expectVal

t3 :: TestTree
t3 = testCase "refer missing relation w\ rename" $
  assertException expectVal output  
  where
    expectVal = RMissingRelation miss
    output = typeOfRQuery (RTRef (rename "R" miss)) sampleRSch
   

t2 :: TestTree
t2 = testCase "refer missing relation" $
  assertException expectVal output  
  where
    expectVal = RMissingRelation miss
    output = typeOfRQuery (RTRef (Rename Nothing miss)) sampleRSch
     -- liftIO $ putStrLn (show output)

-- | empty 
t1 :: TestTree
t1 = testCase "query: ⊥ " $
  do expectVal <- return empty
     output <- typeOfRQuery REmpty sampleRSch 
     output @?= expectVal



-- import Test.HUnit

-- | checks the exceptions.
assertException :: (Exception e, Eq e) => e -> IO a -> IO ()
assertException ex action =
    handleJust isWanted (const $ return ()) $ do
        action
        assertFailure $ "Expected exception: " ++ show ex
  where isWanted = guard . (== ex)

-- testPasses = TestCase $ assertException DivideByZero (evaluate $ 5 `div` 0)
-- testFails  = TestCase $ assertException DivideByZero (evaluate $ 5 `div` 1)

