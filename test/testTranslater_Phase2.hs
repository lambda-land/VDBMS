module TestTranslater_Phase2 where



import Test.Tasty
import Test.Tasty.HUnit


import Prelude hiding (EQ, NEQ ,LT ,LTE , GTE ,GT)
import VDB.Target 
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
import VDB.AlgebraToSql


import Data.Map(Map)
import qualified Data.Map as Map 

import Data.Set (Set)
import qualified Data.Set as Set



-- 
--  ** test transAlgebraToQuery
-- 

testTransAlgebraToQuery :: TestTree
testTransAlgebraToQuery = testGroup "Test transAlgebraToQuery"
  [
    testGroup "1) just projection"
    [  testCase "- Proj a1,a2 (Table1)" $
       do output <- return $ transAlgebraToQuery (  
            Proj [(F.Lit True, 
                   Attribute {attributeName = "a1"})
               ,(F.Lit True,
                   Attribute {attributeName = "a2"})
               ] 
            (TRef (Relation {relationName = "Table1"})) )
          expectVal <- return $
            Select [Attribute {attributeName = "a1"}, Attribute {attributeName = "a2"}] 
            (Where Nothing (From (Relation {relationName = "Table1"})))
          expectVal @=? output
    ]
  , testGroup "2) projection with selection"
    [  testCase "- Proj a1,a2 (Table1)" $
       do output <- return $ transAlgebraToQuery $
            Proj [(F.Lit True, Attribute {attributeName = "a1"})] $ 
            Sel (C.Comp GT 
                  (C.Attr (Attribute {attributeName = "a1"})) 
                  (C.Val (I 5))) $ 
            (TRef (Relation {relationName = "Table2"}))
          expectVal <- return $
            Select [Attribute {attributeName = "a1"}] 
            (Where (Just (And (T.SAT (F.Lit False )) (Comp GT (C.Attr (Attribute {attributeName = "a1"})) (C.Val (I 5))))) 
            (From (Relation {relationName = "Table2"})))

          expectVal @=? output
    ]
    , testGroup "3) have variational condition  "
    [  testCase "- Proj a1 Sel F(a1 > 5, a1 < 5) (Table1)" $ 
       do output <- return $ transAlgebraToQuery $
            Proj [(F.Lit True, Attribute {attributeName = "a1"})] $ 
            Sel (C.CChc (F.Ref (Feature {featureName = "F"})) 
                       (C.Comp GT (C.Attr a1) (C.Val (I 5))) 
                       (C.Comp LT (C.Attr a1) (C.Val (I 5)))) $ 
            (TRef (Relation {relationName = "Table2"}))
          expectVal <- return $ 
            Select [Attribute {attributeName = "a1"}] 
            (QueryOp Union 
              (Where (Just (And (T.SAT (F.Lit False )) 
                                (And (Comp GT (C.Attr (Attribute {attributeName = "course"})) (C.Val (I 5))) 
                                     (T.SAT (F.Ref (Feature "F"))) ))) 
                (From (Relation {relationName = "Table2"}))) 
              (Where (Just (And (T.SAT (F.Lit False ))  
                                (And (Comp LT (C.Attr (Attribute {attributeName = "course"})) (C.Val (I 5))) 
                                    (T.SAT (F.Not (F.Ref (Feature "F")))) ))) 
                (From (Relation {relationName = "Table2"}))))

          expectVal @=? output
    ]
    , testGroup "4) variational query "
    [  testCase "- F<Proj a1 (Table1), Proj a2 (Table2)>" $ 
       do output <- return $ transAlgebraToQuery $
            AChc (F.Ref (Feature {featureName = "F"})) 
             (Proj [(F.Lit True, Attribute {attributeName = "a1"})] (TRef (Relation {relationName = "Table2"}))) 
             (Proj [(F.Lit True, Attribute {attributeName = "a1"})] (TRef (Relation {relationName = "Table2"})))
          expectVal <- return $
            QueryOp Union 
              (Select [Attribute {attributeName = "a1"}] 
                (Where (Just (And (T.SAT (F.Lit False ))   (T.SAT (F.Ref (Feature "F"))) ))  
                  (From (Relation {relationName = "Table2"})))) 
              (Select [Attribute {attributeName = "a1"}] 
                (Where (Just (And (T.SAT (F.Lit False ))   
                                  (T.SAT (F.Not (F.Ref (Feature "F")))) ))   
                (From (Relation {relationName = "Table2"})) ))
          expectVal @=? output
    ]


  ]


