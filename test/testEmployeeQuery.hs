module TestEmployeeQuery where 

import Database.HDBC 

import Test.Tasty
import Test.Tasty.HUnit

import VDB.Translations.VSqlToAlgebra
import VDB.SQL
import VDB.Algebra
import VDB.Name 
import VDB.FeatureExpr 
-- import VDB.Condition 
import VDB.Variational
-- import qualified VDB.Value as V
import VDB.Variational
import VDB.Schema
import VDB.Config
import qualified VDB.Condition as C
import VDB.Type


-- import VDB.Example.EmployeeUseCase.EmployeeSchema
-- import VDB.Example.EmployeeUseCase.EmployeeVSchema
import VDB.Example.EmployeeUseCase.EmployeeQuery
import VDB.Example.EmployeeUseCase.EmployeeVQuery
import VDB.Example.EmployeeUseCase.EmployeeVSchema
import VDB.Example.EmployeeUseCase.EmployeeSchema
import VDB.Example.EmployeeUseCase.SmallSampleForTest

import VDB.TypeSystem.Semantics
import qualified Data.Map as M 
import Data.SBV

import Prelude hiding (Ordering(..))

-- featureExpr rom VDB.Example.EmployeeUseCase.EmployeeVSchema
-- v1,v2,v3,v4,v5 :: FeatureExpr
-- v1 = Ref (Feature "v1")
-- v2 = Ref (Feature "v2")
-- v3 = Ref (Feature "v3")
-- v4 = Ref (Feature "v4")
-- v5 = Ref (Feature "v5")

-- date2000 = SqlUTCTime $ UTCTime (fromGregorian 2000 1 1) 0

--
-- ** small test suite
--
{-
testq1,testq2, testq3, testq4, testq5 :: Algebra

-- SELECT A1 FROM T1
testq1 = Proj [plainAttr "A1" ] $ TRef (Relation "T1")

-- SELECT A2 FROM T2 Where A2 > 5
testq2 =  Proj [plainAttr "A2"] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))

-- SELECT A1, A2 FROM T2 Where A2 > 5
testq2' = Proj [plainAttr "A1",plainAttr "A2" ] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))

-- SELECT A3 FROM T3
testq3 = Proj [plainAttr "A3" ] $ TRef (Relation "T3")

-- (SELECT A1 FROM T2) Union (SELECT A1 FROM T3)
testq4 = SetOp Prod l r 
        where l = Proj [plainAttr "A1" ] $ TRef (Relation "T2")
              r = Proj [plainAttr "A1" ] $ TRef (Relation "T3")

-- SELECT * FROM D,E
testq5 = SetOp Prod (TRef (Relation "D")) (TRef (Relation "E"))

testq6 = SetOp Prod testq2 testq2
-}


                          

testQualifyQuery :: TestTree
testQualifyQuery  = testGroup "Test Qualify Query based on the schema"
  [ testGroup "1) test qualify simple query with simple schema"
    [ testCase "Qualify an empty query" $
      do output    <- return $ qualifyQuery tests1 Empty
         expectVal <- return $ Empty
         expectVal @=? output
    ,
      testCase "Qualify query (SELECT A1 FROM T1) with schema [ T1:(A1,A2)] " $
      do output    <- return $ qualifyQuery tests1 testq1
         expectVal <- return $ Proj [qualifedOptAttribute (Lit True )"T1" "A1"] 
                              (TRef (Relation "T1"))
         expectVal @=? output
    ]
  ]


testEmployeeQuery  :: TestTree
testEmployeeQuery  = testGroup "Test fold a list of query to V-query"
  [ testGroup "1) test simple query to V-query"
    [ testCase "fold a empty query list" $
      do output    <- return $ variationizeQuery [ ]
         expectVal <- return $ Empty
         expectVal @=? output
    ,
      testCase "fold a single Query without condition  (SELECT A1 FROM T1)" $
      do output    <- return $ variationizeQuery [testq1]
         expectVal <- return $ Proj [(v1,Attribute Nothing "A1")] 
                               (AChc v1 (TRef (Relation "T1")) Empty)
         expectVal @=? output
    ,
      testCase "fold a single Query with condition  (SELECT A1 FROM T2 WHERE A2 > 5)" $
      do output    <- return $ variationizeQuery [testq2]
         expectVal <- return $ Proj [(v1,Attribute Nothing "A2")] 
                               (Sel (C.CChc v1 (C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))) (C.Lit True)) 
                               (AChc v1 (TRef (Relation "T2")) Empty))
         expectVal @=? output
    ,
      testCase "fold two query with different product and different projection " $
      do output    <- return $ variationizeQuery [testq1, testq2]
         expectVal <- return $ Proj [(v1,Attribute Nothing "A1"),(v2,Attribute Nothing "A2")] 
                               (Sel (C.CChc v2 (C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))) (C.Lit True)) 
                               (AChc v2 (TRef (Relation "T2")) (AChc v1 (TRef (Relation "T1")) Empty)))
         expectVal @=? output
    ,
      testCase "fold two query with same product and common attributes" $
      do output    <- return $ variationizeQuery [testq2, testq2']
         expectVal <- return $ Proj [(v2,Attribute Nothing "A1"),(v1 `Or` v2,Attribute Nothing "A2")] 
                               (Sel (C.CChc (v1 `Or` v2) (C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))) (C.Lit True)) 
                               (AChc (v1 `Or` v2) (TRef (Relation "T2")) Empty))
         expectVal @=? output
    ,
      testCase "fold two query which involved with set operation" $
      do output    <- return $ variationizeQuery [testq3,testq4] 
         expectVal <- return $ SetOp Prod 
                                 (Proj [(v2,Attribute Nothing "A1"),(v1,Attribute Nothing "A3")] 
                                  (AChc v2 (TRef (Relation "T2")) (AChc v1 (TRef (Relation "T3")) Empty))) 
                                 (Proj [(v2,Attribute Nothing "A1"),(v1,Attribute Nothing "A3")] 
                                  (AChc (v1 `Or` v2) (TRef (Relation "T3")) Empty))
         expectVal @=? output 

    ]
  ,  
    testGroup "2) test Queries in employee schema"
    [ testCase "test emp query 1 and 2" $
        do output    <- return $ variationizeQuery [empQ1_v1, empQ1_v2]
           expectVal <- return $ Proj [(v1 `Or` v2, Attribute Nothing "empno"),(v1 `Or` v2, Attribute Nothing "hiredate"),(v1 `Or` v2,Attribute Nothing "name")] 
                                  (Sel (C.CChc (v1 `Or` v2) (C.Comp LT (C.Attr (Attribute Nothing "hiredate")) (C.Val date2000)) (C.Lit True)) 
                                    (AChc v2 (TRef (Relation "empacct")) (AChc v1 (TRef (Relation  "otherpersonnel")) Empty)))
           expectVal @=? output 
    , testCase "test emp query 1 to 5" $ 
        do output    <- return $ variationizeQuery [empQ1_v1, empQ1_v2,empQ1_v3,empQ1_v4,empQ1_v5]
           expectVal <- return $ Proj [ (v1 `Or` (v2 `Or` (v3 `Or` (v4 `Or` v5))), unQualifedAttribute "empno")
                                      , (v5,unQualifedAttribute "firstname")
                                      , (v1 `Or` (v2 `Or` (v3 `Or` (v4 `Or` v5))),unQualifedAttribute "hiredate")
                                      , (v5,unQualifedAttribute "lastname")
                                      , (v1 `Or` (v2 `Or` (v3 `Or` v4)), unQualifedAttribute "name")] 
                                   (Sel (C.CChc (v1 `Or` (v2 `Or` v3)) 
                                          (C.Comp LT (C.Attr (unQualifedAttribute "hiredate")) (C.Val date2000)) 
                                          (C.CChc (v4 `Or`v5)  
                                            (C.And 
                                              (C.Comp EQ (C.Attr (qualifedAttribute "empacct" "empno")) (C.Attr (qualifedAttribute "empbio" "empno"))) 
                                              (C.Comp LT (C.Attr (unQualifedAttribute "hiredate")) (C.Val date2000))) 
                                            (C.Lit True)))                                    
                                   (SetOp Prod 
                                      (SetOp Prod (AChc (v2 `Or` (v3 `Or` (v4 `Or` v5))) (TRef (Relation "empacct")) (AChc v1 (TRef (Relation "otherpersonnel")) Empty)) 
                                                  (AChc (v2 `Or` (v3 `Or` v5)) (TRef (Relation "empacct")) (AChc v1 (TRef (Relation "otherpersonnel")) Empty))) 
                                      (SetOp Prod (AChc v5 (TRef (Relation "empbio")) (AChc v1 (TRef (Relation "otherpersonnel")) Empty)) 
                                                  (AChc (v4 `Or` v5) (TRef (Relation "empbio")) (AChc v1 (TRef (Relation "otherpersonnel")) Empty))) 
                                    ) 
                                  )
 
           expectVal @=? output                                                              
    ]


  
  ]
