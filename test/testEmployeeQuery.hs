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

import VDB.TypeSystem.Semantics
import qualified Data.Map as M 
import Data.SBV

import Prelude hiding (Ordering(..))

-- featureExpr rom VDB.Example.EmployeeUseCase.EmployeeVSchema
v1,v2,v3,v4,v5 :: FeatureExpr
v1 = Ref (Feature "v1")
v2 = Ref (Feature "v2")
v3 = Ref (Feature "v3")
v4 = Ref (Feature "v4")
v5 = Ref (Feature "v5")

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
         where cond = C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))

-- SELECT A1, A2 FROM T2 Where A2 > 5
testq2' = Proj [plainAttr "A1",plainAttr "A2" ] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))

-- SELECT A3 FROM T3
testq3 = Proj [plainAttr "A3" ] $ TRef (Relation "T3")

-- (SELECT A1 FROM T2) Union (SELECT A1 FROM T3)
testq4 = SetOp Prod l r 
        where l = Proj [plainAttr "A1" ] $ TRef (Relation "T2")
              r = Proj [plainAttr "A1" ] $ TRef (Relation "T3")

-- SELECT * FROM D,E
testq5 = SetOp Prod (TRef (Relation "D")) (TRef (Relation "E"))
-}

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
         expectVal <- return $ Proj [(v1,Attribute "A1")] 
                               (AChc v1 (TRef (Relation "T1")) Empty)
         expectVal @=? output
    ,
      testCase "fold a single Query with condition  (SELECT A1 FROM T2 WHERE A2 > 5)" $
      do output    <- return $ variationizeQuery [testq2]
         expectVal <- return $ Proj [(v1,Attribute "A2")] 
                               (Sel (C.CChc v1 (C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))) (C.Lit True)) 
                               (AChc v1 (TRef (Relation "T2")) Empty))
         expectVal @=? output
    ,
      testCase "fold two query with different product and different projection " $
      do output    <- return $ variationizeQuery [testq1, testq2]
         expectVal <- return $ Proj [(v1,Attribute "A1"),(v2,Attribute "A2")] 
                               (Sel (C.CChc v2 (C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))) (C.Lit True)) 
                               (AChc v2 (TRef (Relation "T2")) (AChc v1 (TRef (Relation "T1")) Empty)))
         expectVal @=? output
    ,
      testCase "fold two query with same product and common attributes" $
      do output    <- return $ variationizeQuery [testq2, testq2']
         expectVal <- return $ Proj [(v2,Attribute "A1"),(v1 `Or` v2,Attribute "A2")] 
                               (Sel (C.CChc (v1 `Or` v2) (C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))) (C.Lit True)) 
                               (AChc (v1 `Or` v2) (TRef (Relation "T2")) Empty))
         expectVal @=? output
    ,
      testCase "fold two query which involved with set operation" $
      do output    <- return $ variationizeQuery [testq3,testq4] 
         expectVal <- return $ SetOp Prod 
                                 (Proj [(v2,Attribute "A1"),(v1,Attribute "A3")] 
                                  (AChc v2 (TRef (Relation "T2")) (AChc v1 (TRef (Relation "T3")) Empty))) 
                                 (Proj [(v2,Attribute "A1"),(v1,Attribute "A3")] 
                                  (AChc (v1 `Or` v2) (TRef (Relation "T3")) Empty))
         expectVal @=? output 

    ]
  ,  
    testGroup "2) test Queries in employee schema"
    [ testCase "test emp query 1 and 2" $
        do output    <- return $ variationizeQuery [empQ1_v1, empQ1_v2]
           expectVal <- return $ Proj [(v1 `Or` v2, Attribute "empno"),(v1 `Or` v2,Attribute "hiredate"),(v1 `Or` v2,Attribute "name")] 
                                  (Sel (C.CChc (v1 `Or` v2) (C.Comp LT (C.Attr (Attribute "hiredate")) (C.Val date2000)) (C.Lit True)) 
                                    (AChc v2 (TRef (Relation "empacct")) (AChc v1 (TRef (Relation  "otherpersonnel")) Empty)))
           expectVal @=? output 
    -- , testCase "test emp query 1 and 2" $ 
    --     do output    <- return $ variationizeQuery [empQ1_v1, empQ1_v2,empQ1_v3,empQ1_v4,empQ1_v5]
    --        expectVal <- return $ variationizeQuery [empQ1_v1, empQ1_v2,empQ1_v3,empQ1_v4,empQ1_v5]
    --        expectVal @=? output 
    ]

  --   , testCase "test entire (5) emp schemas" $
  --      do output   <- return $ variationizeSchema [empSchema1, empSchema2, empSchema3, empSchema4, empSchema5]
  --         expectVal <- return $ (v1 <+> v2 <+> v3 <+> v4 <+> v5, 
  --                                 M.fromList [(Relation "engineerpersonnel",(v1,
  --                                                M.fromList [ (Attribute "empno",   (v1,TInt32))
  --                                                           , (Attribute "name",    (v1,TString))
  --                                                           , (Attribute "hiredate",(v1,TString))
  --                                                           , (Attribute "title",   (v1,TString))
  --                                                           , (Attribute "deptname",(v1,TString))
  --                                                           ]))
  --                                            ,(Relation "otherpersonnel",(v1,
  --                                                 M.fromList[ (Attribute "empno",   (v1, TInt32))
  --                                                           , (Attribute "name",    (v1, TString))
  --                                                           , (Attribute "hiredate",(v1, TString))
  --                                                           , (Attribute "title",   (v1, TString))
  --                                                           , (Attribute "deptname",(v1, TString))
  --                                                           ]))
  --                                            ,(Relation "job",(v1 `Or` v2 `Or` v3 `Or` v4,
  --                                               M.fromList [   (Attribute "salary", (v1 `Or` v2 `Or` v3 `Or` v4, TInt32))
  --                                                           ,  (Attribute "title",  (v1 `Or` v2 `Or` v3 `Or` v4, TString))
  --                                                           ]))
  --                                            ,(Relation "empacct",(v2 `Or` v3 `Or` v4 `Or` v5,
  --                                               M.fromList[ (Attribute "deptname",  (v2, TString))
  --                                                         , (Attribute "deptno",    (v3 `Or` v4 `Or` v5, TInt32))
  --                                                         , (Attribute "empno",     (v2 `Or` v3 `Or` v4 `Or` v5, TInt32))
  --                                                         , (Attribute "hiredate",  (v2 `Or` v3 `Or` v4 `Or` v5, TString))
  --                                                         , (Attribute "name",      (v2 `Or` v3 , TString)) 
  --                                                         , (Attribute "salary",    (v5, TInt32)) 
  --                                                         , (Attribute "title",     (v2 `Or` v3 `Or` v4`Or` v5, TString))
  --                                                        ]))    
  --                                            ,(Relation "dept",(v3 `Or` v4 `Or` v5,
  --                                               M.fromList  [ (Attribute "deptname", (v3 `Or` v4 `Or` v5, TString))
  --                                                           , (Attribute "deptno", (v3 `Or` v4 `Or` v5, TInt32))
  --                                                           , (Attribute "managerno", (v3 `Or` v4 `Or` v5, TInt32))
  --                                                           ]))   
  --                                            ,(Relation "empbio",        (v4 `Or` v5,
  --                                               M.fromList [ (Attribute "birthdate", (v4 `Or` v5, TString))
  --                                                          , (Attribute "empno",     (v4 `Or` v5, TInt32))
  --                                                          , (Attribute "firstname" ,(v5, TString))
  --                                                          , (Attribute "lastname" , (v5, TString))
  --                                                          , (Attribute "name" ,     (v4, TString))
  --                                                          , (Attribute "sex",       (v4 `Or` v5, TString))
  --                                                          ]))   
  --                                          ])
  --         expectVal @=? output

  --   ]
  ]


-- testEmployeeSelection  :: TestTree
-- testEmployeeSelection  = testGroup "Test selection among v-schema"
--   [  
--     testGroup "1) Do selection from Employee v-schema"
--     [ testCase "select v1 from v1 version schema" $
--       do output   <- return $ configureOpt (enable (Feature "v1") disableAll) $ variationizeSchema [empSchema1]
--          expectVal <- return $  Just (M.fromList [(Relation "engineerpersonnel",(v1,
--                                                     M.fromList[ (Attribute "empno",   (v1,TInt32))
--                                                               , (Attribute "name",    (v1,TString))
--                                                               , (Attribute "hiredate",(v1,TString))
--                                                               , (Attribute "title",   (v1,TString))
--                                                               , (Attribute "deptname",(v1,TString))
--                                                               ]))
--                                                  ,(Relation "otherpersonnel",(v1,
--                                                     M.fromList[ (Attribute "empno", (v1, TInt32))
--                                                               , (Attribute "name", (v1, TString))
--                                                               , (Attribute "hiredate", (v1, TString))
--                                                               , (Attribute "title", (v1, TString))
--                                                               , (Attribute "deptname", (v1, TString))
--                                                               ]))
--                                                  ,(Relation "job",(v1,
--                                                     M.fromList[  -- (v1, (Attribute "salary", TInt32)) -- the element order matters in test 
--                                                                  (Attribute "title",   (v1, TString))
--                                                               ,  (Attribute "salary" , (v1, TInt32)) 
--                                                               ]))                                                        
--                                                  ])
--          expectVal @=? output
--     -- wrong answer
--     -- , testCase "select v2 from v1 v2 version schema" $
--     --   do output   <- return $ configureOpt (enable (Feature "v2") disableAll) $ variationizeSchema [empSchema1, empSchema2]
--     --      expectVal <- return $  Just $ M.fromList [(Relation "job",(v2,
--     --                                                   [  (v2, (Attribute "salary", TInt32))
--     --                                                   ,  (v2, (Attribute "title", TString))
--     --                                                   -- , (v1 `Or` v2, (Attribute "salary", TInt32)) -- the element order matters in test 
--     --                                                   ]))
--     --                                               ,(Relation "empacct",(v2,
--     --                                                   [ (v2, (Attribute "empno", TInt32))
--     --                                                   , (v2, (Attribute "name", TString))
--     --                                                   , (v2, (Attribute "hiredate", TString))
--     --                                                   , (v2, (Attribute "title", TString))
--     --                                                   , (v2, (Attribute "deptname", TString))
--     --                                                  ]))                                                         
--     --                                              ]
--     --      expectVal @=? output

--     ]
--    ]



--   