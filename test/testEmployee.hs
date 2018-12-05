module TestEmployee where 

import Test.Tasty
import Test.Tasty.HUnit

import VDB.Translations.VSqlToAlgebra
import VDB.SQL
import VDB.Algebra
import VDB.Name 
import VDB.FeatureExpr 
-- import VDB.Condition 
import VDB.Variational
import qualified VDB.Value as V
import VDB.Variational
import VDB.Schema
import VDB.Config
import VDB.Value 

import VDB.Example.EmployeeUseCase.EmployeeSchema
import VDB.Example.EmployeeUseCase.EmployeeVSchema

import VDB.TypeSystem.Semantics
import qualified Data.Map as M 

-- featureExpr rom VDB.Example.EmployeeUseCase.EmployeeVSchema
-- v1,v2,v3,v4,v5 :: FeatureExpr
-- v1 = Ref (Feature "v1")
-- v2 = Ref (Feature "v2")
-- v3 = Ref (Feature "v3")
-- v4 = Ref (Feature "v4")
-- v5 = Ref (Feature "v5")


testEmployeeSchema  :: TestTree
testEmployeeSchema  = testGroup "Test fold a list of Schema to V-Schema"
  [ testGroup "1) test simple schemas to V-Schema  "
    [ testCase "fold a empty list" $
      do output    <- return $ variationizeSchema [ ]
         expectVal <- return $ (Lit False, M.fromList [ ])
         expectVal @=? output
    ,
      testCase "fold a single schema" $
      do output    <- return $ variationizeSchema [ ( v1, M.fromList [ (Relation "T1", (Lit True,  
                                                                  [ (Lit True, (Attribute "A1", TInt))
                                                                  , (Lit True, (Attribute "A2", TString))]))])]
         expectVal <- return $ (v1, M.fromList [(Relation "T1",(v1,
                                                 [(v1,(Attribute "A1",TInt)),
                                                  (v1,(Attribute "A2",TString))]))])

         expectVal @=? output
    ,
      testCase "fold two schema with same table and totally different attributes" $
      do output    <- return $ variationizeSchema [ ( v1, M.fromList [ (Relation "T1", (Lit True,  
                                                                  [ (Lit True, (Attribute "A1", TInt))
                                                                  , (Lit True, (Attribute "A2", TString))]))])
                                            , ( v2, M.fromList [ (Relation "T1", (Lit True,  
                                                                  [ (Lit True, (Attribute "A3", TInt))
                                                                  , (Lit True, (Attribute "A4", TString))]))])
                                            ]
         expectVal <- return $ (v1 `Or` v2, M.fromList [(Relation "T1",(v1 `Or` v2,
                                                          [(v1,(Attribute "A1",TInt))
                                                          ,(v1,(Attribute "A2",TString))
                                                          ,(v2,(Attribute "A3",TInt))
                                                          ,(v2,(Attribute "A4",TString))
                                                          ]))])
         expectVal @=? output
    ,
      testCase "fold two schema with same table and some common attributes" $
      do output    <- return $ variationizeSchema [ ( v1, M.fromList [ (Relation "T1", (Lit True,  
                                                                  [ (Lit True, (Attribute "A1", TInt))
                                                                  , (Lit True, (Attribute "A2", TString))]))])
                                            , ( v2, M.fromList [ (Relation "T1", (Lit True,  
                                                                  [ (Lit True, (Attribute "A1", TInt))
                                                                  , (Lit True, (Attribute "A3", TString))]))])
                                            ]
         expectVal <- return $ (v1 `Or` v2, M.fromList [(Relation "T1",(v1 `Or` v2,
                                                          [(v1 `Or` v2,(Attribute "A1",TInt))
                                                          ,(v1,        (Attribute "A2",TString))
                                                          ,(v2,        (Attribute "A3",TString))
                                                          ]))])
         expectVal @=? output
    ,
      testCase "fold two schema with different table with some common attributes" $
      do output    <- return $ variationizeSchema [ ( v1, M.fromList [ (Relation "T1", (Lit True,  
                                                                  [ (Lit True, (Attribute "A1", TInt))
                                                                  , (Lit True, (Attribute "A2", TString))]))])
                                            , ( v2, M.fromList [ (Relation "T2", (Lit True,  
                                                                  [ (Lit True, (Attribute "A1", TInt))
                                                                  , (Lit True, (Attribute "A3", TString))]))])
                                            ]
         expectVal <- return $ (v1 `Or` v2, M.fromList [(Relation "T1",(v1,
                                                          [(v1,(Attribute "A1",TInt))
                                                          ,(v1,(Attribute "A2",TString))
                                                          ]))
                                                       ,(Relation "T2",(v2,
                                                          [(v2,(Attribute "A1",TInt))
                                                          ,(v2,(Attribute "A3",TString))
                                                          ]))
                                                       ])
         expectVal @=? output 

    ]
  ,  
    testGroup "2) test in employee schema"
    [ testCase "test emp schema 1 and 2" $
        do output    <- return $ variationizeSchema [empSchema1, empSchema2]
           expectVal <- return $ (v1 `Or` v2, M.fromList [(Relation "engineerpersonnel",(v1,
                                                            [ (v1,(Attribute "empno",TInt))
                                                            , (v1,(Attribute "name",TString))
                                                            , (v1,(Attribute "hiredate",TString))
                                                            , (v1,(Attribute "title",TString))
                                                            , (v1,(Attribute "deptname",TString))
                                                            ]))
                                                         ,(Relation "otherpersonnel",(v1,
                                                            [ (v1, (Attribute "empno", TInt))
                                                            , (v1, (Attribute "name", TString))
                                                            , (v1, (Attribute "hiredate", TString))
                                                            , (v1, (Attribute "title", TString))
                                                            , (v1, (Attribute "deptname", TString))
                                                            ]))
                                                         ,(Relation "job",(v1 `Or` v2,
                                                            [  (v1 `Or` v2, (Attribute "salary", TInt))
                                                            ,  (v1 `Or` v2, (Attribute "title", TString))
                                                            -- , (v1 `Or` v2, (Attribute "salary", TInt)) -- the element order matters in test 
                                                            ]))
                                                         ,(Relation "empacct",(v2,
                                                            [ (v2, (Attribute "empno", TInt))
                                                            , (v2, (Attribute "name", TString))
                                                            , (v2, (Attribute "hiredate", TString))
                                                            , (v2, (Attribute "title", TString))
                                                            , (v2, (Attribute "deptname", TString))
                                                           ]))                                                         
                                                       ])
           expectVal @=? output 

    , testCase "test entire (5) emp schemas" $
       do output   <- return $ variationizeSchema [empSchema1, empSchema2, empSchema3, empSchema4, empSchema5]
          expectVal <- return $ (v1 `Or` v2 `Or` v3 `Or` v4 `Or` v5, 
                                  M.fromList [(Relation "engineerpersonnel",(v1,
                                                [ (v1,(Attribute "empno",TInt))
                                                , (v1,(Attribute "name",TString))
                                                , (v1,(Attribute "hiredate",TString))
                                                , (v1,(Attribute "title",TString))
                                                , (v1,(Attribute "deptname",TString))
                                                ]))
                                             ,(Relation "otherpersonnel",(v1,
                                                [ (v1, (Attribute "empno", TInt))
                                                , (v1, (Attribute "name", TString))
                                                , (v1, (Attribute "hiredate", TString))
                                                , (v1, (Attribute "title", TString))
                                                , (v1, (Attribute "deptname", TString))
                                                ]))
                                             ,(Relation "job",(v1 `Or` v2 `Or` v3 `Or` v4,
                                                [  (v1 `Or` v2 `Or` v3 `Or` v4, (Attribute "salary", TInt))
                                                ,  (v1 `Or` v2 `Or` v3 `Or` v4, (Attribute "title", TString))
                                                -- , (v1 `Or` v2, (Attribute "salary", TInt)) -- the element order matters in test 
                                                ]))
                                             ,(Relation "empacct",(v2 `Or` v3 `Or` v4 `Or` v5,
                                                [ (v2,                         (Attribute "deptname", TString))
                                                , (v3 `Or` v4 `Or` v5,         (Attribute "deptno", TInt))
                                                , (v2 `Or` v3 `Or` v4 `Or` v5, (Attribute "empno", TInt))
                                                , (v2 `Or` v3 `Or` v4 `Or` v5, (Attribute "hiredate", TString))
                                                , (v2 `Or` v3 ,                (Attribute "name", TString)) 
                                                , (v5,                         (Attribute "salary", TInt)) 
                                                , (v2 `Or` v3 `Or` v4`Or` v5,  (Attribute "title", TString))
                                               ]))    
                                             ,(Relation "dept",(v3 `Or` v4 `Or` v5,
                                                [ (v3 `Or` v4 `Or` v5, (Attribute "deptname", TString))
                                                , (v3 `Or` v4 `Or` v5, (Attribute "deptno", TInt))
                                                , (v3 `Or` v4 `Or` v5, (Attribute "managerno", TInt))
                                                ]))   
                                             ,(Relation "empbio",(v4 `Or` v5,
                                               [ (v4 `Or` v5, (Attribute "birthdate", TString))
                                               , (v4 `Or` v5, (Attribute "empno", TInt))
                                               , (v5 ,        (Attribute "firstname", TString))
                                               , (v5 ,        (Attribute "lastname", TString))
                                               , (v4 ,        (Attribute "name", TString))
                                               , (v4 `Or` v5, (Attribute "sex", TString))
                                               ]))   
                                           ])
          expectVal @=? output

    ]
  ]


testEmployeeSelection  :: TestTree
testEmployeeSelection  = testGroup "Test selection among v-schema"
  [  
    testGroup "1) Do selection from Employee v-schema"
    [ testCase "select v1 from v1 version schema" $
      do output   <- return $ configureOpt (enable (Feature "v1") disableAll) $ variationizeSchema [empSchema1]
         expectVal <- return $  Just (M.fromList [(Relation "engineerpersonnel",(v1,
                                                    [ (v1,(Attribute "empno",TInt))
                                                    , (v1,(Attribute "name",TString))
                                                    , (v1,(Attribute "hiredate",TString))
                                                    , (v1,(Attribute "title",TString))
                                                    , (v1,(Attribute "deptname",TString))
                                                    ]))
                                                 ,(Relation "otherpersonnel",(v1,
                                                    [ (v1, (Attribute "empno", TInt))
                                                    , (v1, (Attribute "name", TString))
                                                    , (v1, (Attribute "hiredate", TString))
                                                    , (v1, (Attribute "title", TString))
                                                    , (v1, (Attribute "deptname", TString))
                                                    ]))
                                                 ,(Relation "job",(v1,
                                                    [  -- (v1, (Attribute "salary", TInt)) -- the element order matters in test 
                                                       (v1, (Attribute "title", TString))
                                                    ,  (v1 , (Attribute "salary", TInt)) 
                                                    ]))                                                        
                                                 ])
         expectVal @=? output
    -- wrong answer
    -- , testCase "select v2 from v1 v2 version schema" $
    --   do output   <- return $ configureOpt (enable (Feature "v2") disableAll) $ variationizeSchema [empSchema1, empSchema2]
    --      expectVal <- return $  Just $ M.fromList [(Relation "job",(v2,
    --                                                   [  (v2, (Attribute "salary", TInt))
    --                                                   ,  (v2, (Attribute "title", TString))
    --                                                   -- , (v1 `Or` v2, (Attribute "salary", TInt)) -- the element order matters in test 
    --                                                   ]))
    --                                               ,(Relation "empacct",(v2,
    --                                                   [ (v2, (Attribute "empno", TInt))
    --                                                   , (v2, (Attribute "name", TString))
    --                                                   , (v2, (Attribute "hiredate", TString))
    --                                                   , (v2, (Attribute "title", TString))
    --                                                   , (v2, (Attribute "deptname", TString))
    --                                                  ]))                                                         
    --                                              ]
    --      expectVal @=? output

    ]
   ]

  