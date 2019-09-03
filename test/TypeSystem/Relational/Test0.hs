module TypeSystem.Relational.Test0 where

import VDB.Schema.Relational.Sample

import VDBMS.TypeSystem.Relational.TypeSystem 
import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Schema.Relational.Types
import VDBMS.VDB.Name
import VDBMS.VDB.GenName

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
uts = testGroup "Unit tests" [t1, t2, t3]

t3 :: TestTree
t3 = testCase "referring to a missing relation with rename" $
  assertException expectVal output  
  where
    expectVal = RMissingRelation miss
    output = typeOfRQuery (RTRef (rename "R" miss)) sampleRSch
   

t2 :: TestTree
t2 = testCase "referring to a missing relation" $
  assertException expectVal output  
  where
    expectVal = RMissingRelation miss
    output = typeOfRQuery (RTRef (Rename Nothing miss)) sampleRSch
     -- liftIO $ putStrLn (show output)

t1 :: TestTree
t1 = testCase "empty query" $
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

