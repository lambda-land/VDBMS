module TestEmployeeSchema where 

import Test.Tasty
import Test.Tasty.HUnit

import VDB.Translations.VSqlToAlgebra
import VDB.SQL
import VDB.Algebra
import VDB.Name 
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDB.Variational
import VDB.Schema
import VDB.Config
import VDB.Type


import VDB.Example.EmployeeUseCase.EmployeeSchema
import VDB.Example.EmployeeUseCase.EmployeeVSchema
import VDB.Example.EmployeeUseCase.SmallSampleForTest


import VDB.TypeSystem.Semantics
import qualified Data.Map as M 
import Data.SBV




testEmployeeSchema  :: TestTree
testEmployeeSchema  = testGroup "Test fold a list of Schema to V-Schema"
  [ testGroup "1) test simple schemas to V-Schema  "
    [ testCase "fold a empty list" $
      do output    <- return $ variationizeSchema [ ]
         expectVal <- return $ (Lit False, M.fromList [ ])
         expectVal @=? output
    ,
      testCase "fold a single schema" $
      do output    <- return $ variationizeSchema [ ( v1,  M.fromList[ (Relation "T1", (Lit True,  
                                                                  M.fromList[ (Attribute Nothing "A1", (Lit True, TInt32))
                                                                            , (Attribute Nothing "A2", (Lit True, TString))]))])]
         expectVal <- return $ (v1, M.fromList [(Relation "T1",(v1,
                                                 M.fromList [(Attribute Nothing "A1", (v1,TInt32)),
                                                            (Attribute Nothing "A2", (v1,TString))]))])

         expectVal @=? output
    ,
      testCase "fold two schema with same table and totally different attributes" $
      do output    <- return $ variationizeSchema [ ( v1, M.fromList [ (Relation "T1", (Lit True,  
                                                                  M.fromList[ (Attribute Nothing "A1", (Lit True, TInt32))
                                                                            , (Attribute Nothing "A2", (Lit True, TString))]))])
                                            , ( v2, M.fromList [ (Relation "T1", (Lit True,  
                                                                  M.fromList[ (Attribute Nothing "A3", (Lit True, TInt32))
                                                                            , (Attribute Nothing "A4", (Lit True, TString))]))])
                                            ]
         expectVal <- return $ (v1 <+> v2, M.fromList [(Relation "T1",(v1 `Or` v2,
                                                          M.fromList[(Attribute Nothing "A1",(v1,TInt32))
                                                                    ,(Attribute Nothing "A2",(v1,TString))
                                                                    ,(Attribute Nothing "A3",(v2,TInt32))
                                                                    ,(Attribute Nothing "A4",(v2,TString))
                                                                    ]))])
         expectVal @=? output
    ,
      testCase "fold two schema with same table and some common attributes" $
      do output    <- return $ variationizeSchema [ ( v1, M.fromList [ (Relation "T1", (Lit True,  
                                                                  M.fromList [ (Attribute Nothing "A1", (Lit True, TInt32))
                                                                             , (Attribute Nothing "A2", (Lit True, TString))]))])
                                            , ( v2, M.fromList [ (Relation "T1", (Lit True,  
                                                                  M.fromList [ (Attribute Nothing "A1", (Lit True, TInt32))
                                                                             , (Attribute Nothing "A3", (Lit True, TString))]))])
                                            ]
         expectVal <- return $ (v1 <+> v2, M.fromList [(Relation "T1",(v1 `Or` v2,
                                                          M.fromList  [(Attribute Nothing "A1", (v1 `Or` v2,TInt32))
                                                                      ,(Attribute Nothing "A2", (v1,TString))
                                                                      ,(Attribute Nothing "A3", (v2,TString))
                                                                      ]))])
         expectVal @=? output
    ,
      testCase "fold two schema with different table with some common attributes" $
      do output    <- return $ variationizeSchema [ ( v1, M.fromList [ (Relation "T1", (Lit True,  
                                                                  M.fromList [ (Attribute Nothing "A1", (Lit True, TInt32))
                                                                             , (Attribute Nothing "A2", (Lit True, TString))]))])
                                                   , ( v2, M.fromList [ (Relation "T2", (Lit True,  
                                                                  M.fromList [  (Attribute Nothing "A1", (Lit True, TInt32))
                                                                              , (Attribute Nothing "A3", (Lit True, TString))]))])
                                               ]
         expectVal <- return $ (v1 <+> v2, M.fromList [(Relation "T1",(v1,
                                                          M.fromList [(Attribute Nothing "A1",(v1,TInt32))
                                                                      ,(Attribute Nothing "A2",(v1,TString))
                                                                      ]))
                                                       ,(Relation "T2",(v2,
                                                          M.fromList [(Attribute Nothing "A1",(v2,TInt32))
                                                                      ,(Attribute Nothing "A3",(v2,TString))
                                                                      ]))
                                                       ])
         expectVal @=? output 

    ]
  ,  
    testGroup "2) test in employee schema"
    [ testCase "test emp schema 1 and 2" $
        do output    <- return $ variationizeSchema [empSchema1, empSchema2]
           expectVal <- return $ (v1 <+> v2, M.fromList [(Relation "engineerpersonnel",(v1,
                                                            M.fromList[ (qualifedAttribute "engineerpersonnel" "empno",(v1,TInt32))
                                                                      , (qualifedAttribute "engineerpersonnel" "name",(v1,TString))
                                                                      , (qualifedAttribute "engineerpersonnel" "hiredate",(v1,TUTCTime))
                                                                      , (qualifedAttribute "engineerpersonnel" "title",(v1,TString))
                                                                      , (qualifedAttribute "engineerpersonnel" "deptname",(v1,TString))
                                                                      ]))
                                                         ,(Relation "otherpersonnel",(v1,
                                                            M.fromList[ (qualifedAttribute "otherpersonnel" "empno", (v1, TInt32))
                                                            , (qualifedAttribute "otherpersonnel" "name",            (v1, TString))
                                                            , (qualifedAttribute "otherpersonnel" "hiredate",        (v1, TUTCTime))
                                                            , (qualifedAttribute "otherpersonnel" "title",           (v1, TString))
                                                            , (qualifedAttribute "otherpersonnel" "deptname",        (v1, TString))
                                                            ]))
                                                         ,(Relation "job",(v1 `Or` v2,
                                                            M.fromList[  (qualifedAttribute "job" "salary", (v1 `Or` v2, TInt32))
                                                                      ,  (qualifedAttribute "job" "title", (v1 `Or` v2, TString))
                                                                      ]))
                                                         ,(Relation "empacct",(v2,
                                                            M.fromList[ (qualifedAttribute "empacct" "empno",   (v2, TInt32))
                                                                      , (qualifedAttribute "empacct" "name",    (v2, TString))
                                                                      , (qualifedAttribute "empacct" "hiredate",(v2, TUTCTime))
                                                                      , (qualifedAttribute "empacct" "title",   (v2, TString))
                                                                      , (qualifedAttribute "empacct" "deptname",(v2, TString))
                                                                     ]))                                                         
                                                       ])
           expectVal @=? output 

    , testCase "test entire (5) emp schemas" $
       do output   <- return $ variationizeSchema [empSchema1, empSchema2, empSchema3, empSchema4, empSchema5]
          expectVal <- return $ (v1 <+> v2 <+> v3 <+> v4 <+> v5, 
                                  M.fromList [(Relation "engineerpersonnel",(v1,
                                                 M.fromList [ (qualifedAttribute "engineerpersonnel" "empno",   (v1,TInt32))
                                                            , (qualifedAttribute "engineerpersonnel" "name",    (v1,TString))
                                                            , (qualifedAttribute "engineerpersonnel" "hiredate",(v1,TUTCTime))
                                                            , (qualifedAttribute "engineerpersonnel" "title",   (v1,TString))
                                                            , (qualifedAttribute "engineerpersonnel" "deptname",(v1,TString))
                                                            ]))
                                             ,(Relation "otherpersonnel",(v1,
                                                  M.fromList[ (qualifedAttribute "otherpersonnel" "empno",   (v1, TInt32))
                                                            , (qualifedAttribute "otherpersonnel" "name",    (v1, TString))
                                                            , (qualifedAttribute "otherpersonnel" "hiredate",(v1, TUTCTime))
                                                            , (qualifedAttribute "otherpersonnel" "title",   (v1, TString))
                                                            , (qualifedAttribute "otherpersonnel" "deptname",(v1, TString))
                                                            ]))
                                             ,(Relation "job",(v1 `Or` v2 `Or` v3 `Or` v4,
                                                M.fromList [   (qualifedAttribute "job" "salary", (v1 `Or` v2 `Or` v3 `Or` v4, TInt32))
                                                            ,  (qualifedAttribute "job" "title",  (v1 `Or` v2 `Or` v3 `Or` v4, TString))
                                                            ]))
                                             ,(Relation "empacct",(v2 `Or` v3 `Or` v4 `Or` v5,
                                                M.fromList[ (qualifedAttribute "empacct" "deptname",  (v2, TString))
                                                          , (qualifedAttribute "empacct" "deptno",    (v3 `Or` v4 `Or` v5, TInt32))
                                                          , (qualifedAttribute "empacct" "empno",     (v2 `Or` v3 `Or` v4 `Or` v5, TInt32))
                                                          , (qualifedAttribute "empacct" "hiredate",  (v2 `Or` v3 `Or` v4 `Or` v5, TUTCTime))
                                                          , (qualifedAttribute "empacct" "name",      (v2 `Or` v3 , TString)) 
                                                          , (qualifedAttribute "empacct" "salary",    (v5, TInt32)) 
                                                          , (qualifedAttribute "empacct" "title",     (v2 `Or` v3 `Or` v4`Or` v5, TString))
                                                         ]))    
                                             ,(Relation "dept",(v3 `Or` v4 `Or` v5,
                                                M.fromList  [ (qualifedAttribute "dept" "deptname", (v3 `Or` v4 `Or` v5, TString))
                                                            , (qualifedAttribute "dept" "deptno", (v3 `Or` v4 `Or` v5, TInt32))
                                                            , (qualifedAttribute "dept" "managerno", (v3 `Or` v4 `Or` v5, TInt32))
                                                            ]))   
                                             ,(Relation "empbio",        (v4 `Or` v5,
                                                M.fromList [ (qualifedAttribute "empbio" "birthdate", (v4 `Or` v5, TUTCTime))
                                                           , (qualifedAttribute "empbio" "empno",     (v4 `Or` v5, TInt32))
                                                           , (qualifedAttribute "empbio" "firstname" ,(v5, TString))
                                                           , (qualifedAttribute "empbio" "lastname" , (v5, TString))
                                                           , (qualifedAttribute "empbio" "name" ,     (v4, TString))
                                                           , (qualifedAttribute "empbio" "sex",       (v4 `Or` v5, TString))
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
                                                    M.fromList[ (qualifedAttribute "engineerpersonnel" "empno",   (v1,TInt32))
                                                              , (qualifedAttribute "engineerpersonnel" "name",    (v1,TString))
                                                              , (qualifedAttribute "engineerpersonnel" "hiredate",(v1,TUTCTime))
                                                              , (qualifedAttribute "engineerpersonnel" "title",   (v1,TString))
                                                              , (qualifedAttribute "engineerpersonnel" "deptname",(v1,TString))
                                                              ]))
                                                 ,(Relation "otherpersonnel",(v1,
                                                    M.fromList[ (qualifedAttribute "otherpersonnel" "empno", (v1, TInt32))
                                                              , (qualifedAttribute "otherpersonnel" "name", (v1, TString))
                                                              , (qualifedAttribute "otherpersonnel" "hiredate", (v1, TUTCTime))
                                                              , (qualifedAttribute "otherpersonnel" "title", (v1, TString))
                                                              , (qualifedAttribute "otherpersonnel" "deptname", (v1, TString))
                                                              ]))
                                                 ,(Relation "job",(v1,
                                                    M.fromList[  -- (v1, (Attribute Nothing "salary", TInt32)) -- the element order matters in test 
                                                                 (qualifedAttribute "job" "title",   (v1, TString))
                                                              ,  (qualifedAttribute "job" "salary" , (v1, TInt32)) 
                                                              ]))                                                        
                                                 ])
         expectVal @=? output
    -- wrong answer
    -- , testCase "select v2 from v1 v2 version schema" $
    --   do output   <- return $ configureOpt (enable (Feature "v2") disableAll) $ variationizeSchema [empSchema1, empSchema2]
    --      expectVal <- return $  Just $ M.fromList [(Relation "job",(v2,
    --                                                   [  (v2, (Attribute Nothing "salary", TInt32))
    --                                                   ,  (v2, (Attribute Nothing "title", TString))
    --                                                   -- , (v1 `Or` v2, (Attribute Nothing "salary", TInt32)) -- the element order matters in test 
    --                                                   ]))
    --                                               ,(Relation "empacct",(v2,
    --                                                   [ (v2, (Attribute Nothing "empno", TInt32))
    --                                                   , (v2, (Attribute Nothing "name", TString))
    --                                                   , (v2, (Attribute Nothing "hiredate", TUTCTime))
    --                                                   , (v2, (Attribute Nothing "title", TString))
    --                                                   , (v2, (Attribute Nothing "deptname", TString))
    --                                                  ]))                                                         
    --                                              ]
    --      expectVal @=? output

    ]
   ]

  