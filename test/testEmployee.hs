module TestEmployee where 

import Test.Tasty
import Test.Tasty.HUnit

import VDB.VSqlToAlgebra
import VDB.SQL
import VDB.Algebra
import VDB.Name 
import qualified VDB.FeatureExpr as F
import VDB.Condition 
import VDB.Variational
import qualified VDB.Value as V
import VDB.Variational
import VDB.Schema
import VDB.Config
import VDB.Value 


import VDB.Example.TwoOption
import VDB.TypeSystem.Semantics
import qualified Data.Map as Map 



-- | test the schema output from different configuration of A and B. 
--   Where A and B is the feature expression, 
--   and the underlying schema is the one from the Example.TwoOption
testEmployee  :: TestTree
testEmployee  = testGroup "Test the FeatureExpr evaluation among the schema"
  [  
    testGroup "1) disable all first."
    [ testCase "enable v1" $
      do output   <- return $ configureOptList (enable (Feature "v1") disableAll) [schema1,schema2,schema3,schema4, schema5]
         expectVal <- return $ [Map.fromList [(Relation "engineerpersonnel",
                                                  (TRUE,[(TRUE,(Attribute "empno",TInt)),
                                                         (TRUE,(Attribute "name",TString)),
                                                         (TRUE,(Attribute "hiredate",TString)),
                                                         (TRUE,(Attribute "title",TString)),
                                                         (TRUE,(Attribute "deptname",TString))])),
                                               (Relation "job",
                                                  (TRUE,[(TRUE,(Attribute "title",TString)),
                                                         (TRUE,(Attribute "salary",TInt))])),
                                               (Relation "otherpersonnel",
                                                  (TRUE,[(TRUE,(Attribute "empno",TInt)),
                                                         (TRUE,(Attribute "name",TString)),
                                                         (TRUE,(Attribute "hiredate",TString)),
                                                         (TRUE,(Attribute "title",TString)),
                                                         (TRUE,(Attribute "deptname",TString))]))]]
          expectVal @=? output
    , testCase "enable v1 and v2" $
       do output   <- return $ configureOptList (enableMany [(Feature "v1"), (Feature "v2")] disableAll) [schema1,schema2,schema3,schema4, schema5]
          expectVal <- return $ [Map.fromList [(Relation "engineerpersonnel",
                                                  (TRUE,[(TRUE,(Attribute "empno",TInt)),
                                                         (TRUE,(Attribute "name",TString)),
                                                         (TRUE,(Attribute "hiredate",TString)),
                                                         (TRUE,(Attribute "title",TString)),
                                                         (TRUE,(Attribute "deptname",TString))])),
                                                (Relation "job",
                                                  (TRUE,[(TRUE,(Attribute "title",TString)),
                                                         (TRUE,(Attribute "salary",TInt))])),
                                                (Relation "otherpersonnel",
                                                  (TRUE,[(TRUE,(Attribute "empno",TInt)),
                                                         (TRUE,(Attribute "name",TString)),
                                                         (TRUE,(Attribute "hiredate",TString)),
                                                         (TRUE,(Attribute "title",TString)),
                                                         (TRUE,(Attribute "deptname",TString))]))],
                                Map.fromList [(Relation "empacct",
                                                (TRUE,[(TRUE,(Attribute "empno",TInt)),
                                                       (TRUE,(Attribute "name",TString)),
                                                       (TRUE,(Attribute "hiredate",TString)),
                                                       (TRUE,(Attribute "title",TString)),
                                                       (TRUE,(Attribute "deptname",TString))])),
                                              (Relation "job",
                                                (TRUE,[(TRUE,(Attribute "title",TString)),
                                                       (TRUE,(Attribute "salary",TInt))]))]]
          expectVal @=? output

    ]
  -- ,  
  --   testGroup "2) disable all first, then:"
  --   [ testCase "enable A" $
  --      do output   <- return $ semVsch twoOptionSchema (enable (Feature "A") disableAll )
  --         expectVal <- return $ Map.fromList [(Relation "t1", 
  --                                     [ (Attribute "a3", TInt)
  --                                     , (Attribute "a4", TInt)
  --                                     , (Attribute "a7", TInt)
  --                                     , (Attribute "a8", TInt)
  --                                     , (Attribute "a11", TInt)
  --                                     , (Attribute "a12", TInt)
  --                                     , (Attribute "a15", TInt)
  --                                     , (Attribute "a16", TInt)
  --                                     ])]
  --         expectVal @=? output
  --   , testCase "enable B" $
  --      do output   <- return $ semVsch twoOptionSchema (enable (Feature "B") disableAll )
  --         expectVal <- return $ Map.fromList [(Relation "t1", 
  --                                     [ (Attribute "a5", TInt)
  --                                     , (Attribute "a6", TInt)
  --                                     , (Attribute "a7", TInt)
  --                                     , (Attribute "a8", TInt)
  --                                     , (Attribute "a13", TInt)
  --                                     , (Attribute "a14", TInt)
  --                                     , (Attribute "a15", TInt)
  --                                     , (Attribute "a16", TInt)
  --                                     ])]
  --         expectVal @=? output

  --   ]
    
  ]