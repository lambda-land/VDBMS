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

import Database.HDBC (iToSql, nToSql)


-- | test relational type system.
trtypesys :: TestTree
trtypesys = testGroup "Relational Type System Tests" [uts]

-- | Unit tests.
uts :: TestTree
uts = testGroup "Unit tests" [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]

t1, t2, t3, t4, t5, t6, t7, t8, t9 :: TestTree
q0, q1, q2 :: RAlgebra
rq2 :: Rename RAlgebra
env1 :: RTypeEnv 
c1, c1', c1err :: SqlCond RAlgebra

-- 
-- set operation
-- 

-- 
-- projection
-- 

-- 
-- selection
-- 

t6 = testCase "q6: σ (true) R" $
  utest q2 sampleRSch env1

q2 = RSel 
  (SqlCond (RLit True))
  rq2

rq2 = (Rename Nothing q0)

t7 = testCase "q7: σ (A = 2) R" $
  utest q3 sampleRSch env1

t8 = testCase "q8: σ (R.A = 2) R" $
  utest q4 sampleRSch env1

q3 = RSel c1 rq2
q4 = RSel c1' rq2

env1 = fromList [(a, [RAttrInfo TInt64 (RelQualifier r)])]

c1 = SqlCond (RComp EQ (Att (Attr a Nothing))
                       (Val (iToSql 2)))
c1' = SqlCond (RComp EQ (Att (Attr a (Just (RelQualifier r))))
                       (Val (iToSql 2)))
c1err' = SqlCond (RComp EQ (Att (Attr a Nothing))
                           (Val (nToSql 2)))

c1err = SqlCond (RComp EQ (Att (Attr b Nothing))
                          (Val (iToSql 2)))

t9 = testCase "q9: σ (B = 2) R → att not in env" $
  excpTest (RSel c1err rq2) sampleRSch (RAttrNotInTypeEnv b env1) 

t10 = testCase "q10: σ (A = 2.0) R → mismatch types" $ 
  excpTest (RSel c1err' rq2) sampleRSch 
    (RCompInvalid (Att (Attr a Nothing)) TInt64 
                  (Val (iToSql 2))       TInteger
                  env1)

t11 = testCase "q11: σ (R.A = 2) RR → att qual not in env" $
  excpTest (RSel c1' (rename "RR" q0)) sampleRSch
    (RQualNotInInfo (RelQualifier r) [RAttrInfo TInt64 (subqQual "RR")])
-- 
-- join
-- 

-- 
-- production
-- 

-- 
-- relation reference 
-- 

t5 = testCase "q5: RR = R" $ 
  utest q1 sampleRSch (fromList [(a, [RAttrInfo TInt64 (relQual "RR")])])

q1 = RTRef (rename "RR" r)

t4 = testCase "q4: R" $ 
  utest q0 sampleRSch (fromList [(a, [RAttrInfo TInt64 (RelQualifier r)])])

q0 = RTRef (Rename Nothing r) 

t3 = testCase "q3: refer missing relation w rename" $
  excpTest (RTRef (rename "R" miss)) sampleRSch (RMissingRelation miss) 

t2 = testCase "q2: refer missing relation" $
  excpTest (RTRef (Rename Nothing miss)) sampleRSch (RMissingRelation miss)

-- 
-- empty 
-- 
t1 = testCase "q1: ⊥ " $ utest REmpty sampleRSch empty

-- | unit test for relational type system without exceptions.
utest :: RAlgebra -> RSchema -> RTypeEnv -> Assertion 
utest q s t = 
  do output <- typeOfRQuery q s 
     output @?= t

-- | unit test for relational type system for exceptions.
excpTest :: (Exception e, Eq e) => RAlgebra -> RSchema -> e -> IO ()
excpTest q s err = assertException err (typeOfRQuery q s)

-- | checks the exceptions.
assertException :: (Show a, Exception e, Eq e) => e -> IO a -> IO ()
assertException ex action =
    handleJust isWanted (const $ return ()) $ do
        a <- action
        -- liftIO $ putStrLn (show a)
        assertFailure $ "output: " ++ show a
        -- assertFailure $ "Expected exception: " ++ show ex
  where isWanted = guard . (== ex)

-- testPasses = TestCase $ assertException DivideByZero (evaluate $ 5 `div` 0)
-- testFails  = TestCase $ assertException DivideByZero (evaluate $ 5 `div` 1)

