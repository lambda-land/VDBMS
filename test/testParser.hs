module TestParser where 

import Test.Tasty
import Test.Tasty.HUnit

import Text.Megaparsec
-- import Control.Monad.Identity 

import VDB.ParsingSQL
import VDB.Name
import VDB.Value
import Prelude hiding (EQ,LT,GT,compare)

-- 
--  ** test featureExpr
-- 

testFeatureExpr :: TestTree
testFeatureExpr = testGroup "Test featureExpr"
  [testGroup "1) bool"
    [  testCase "- false" 
       (assertEqual "False =? false " (Right $ FLit False) (parse featureExpr "" "false"))
  
    ,  testCase "- true"
       (assertEqual "False =? false " (Right $ FLit True) (parse featureExpr "" "true"))

    ]

    ,
    testGroup "2) feature "
    [  testCase "- featureName: US" $
       do output <- return $ 
            parse featureExpr "" "US"
          expectVal <- return $
            Right $ FRef (Feature {featureName = "US"})
          expectVal @=? output
    ]
    ,
    testGroup "3) NOT featureExpr"
    [  testCase "- !US" $
       do output <- return $ 
            parse featureExpr "" "NOT US"
          expectVal <- return $
            Right $ FNot ( FRef (Feature {featureName = "US"}))
          expectVal @=? output
    ]
    ,
    testGroup "4) featureExpr AND featureExpr"
    [  testCase "- US AND Iran" $
       do output <- return $ 
            parse featureExpr "" "US AND Iran"
          expectVal <- return $
            Right $ FAnd 
                      (FRef (Feature {featureName = "US"})) 
                      (FRef (Feature {featureName = "Iran"}))
          expectVal @=? output
    ]
    ,
    testGroup "5) featureExpr OR featureExpr"
    [  testCase "- US OR Iran" $
       do output <- return $ 
            parse featureExpr "" "US OR Iran"
          expectVal <- return $
            Right $ FOr 
                      (FRef (Feature {featureName = "US"})) 
                      (FRef (Feature {featureName = "Iran"}))
          expectVal @=? output
    ]
    ,
    testGroup "6) test featureExpr combination"
    [  testCase "- (NOT US) AND Iran" $
       do output <- return $ 
            parse featureExpr "" "(NOT US) AND Iran"
          expectVal <- return $
            Right $ FAnd 
                      (FNot (FRef (Feature {featureName = "US"}))) 
                      (FRef (Feature {featureName = "Iran"}))
          expectVal @=? output

       , testCase "- US OR (NOT Iran)" $
         do output <- return $ 
              parse featureExpr "" "US OR (NOT Iran)"
            expectVal <- return $
              Right $ FOr 
                      (FRef (Feature {featureName = "US"}))
                      (FNot (FRef (Feature {featureName = "Iran"}))) 
            expectVal @=? output
    ]
  ]


-- 
--  ** test featureExpr
-- 

testCondition :: TestTree
testCondition = testGroup "Test Condition"
  [  testGroup "1) atom opt atom "
     [  testCase "- price > 2000" $
        do output <- return $ 
             parse condition "" "price > 2000"
           expectVal <- return $
             Right $ CComp GT (Val (S "price")) (Val (I 2000))
           expectVal @=? output

     ,  testCase "- isEncrypted = true" $
        do output <- return $ 
             parse condition "" "isEncrypted = true"
           expectVal <- return $
             Right $ CComp EQ (Val (S "isEncrypted")) (Val (B True))
           expectVal @=? output
    ]
  ,
    testGroup "2) NOT condition "
    [  testCase "- NOT true" $
       do output <- return $ 
            parse condition "" "NOT true"
          expectVal <- return $
            Right $ CNot (CLit True)
          expectVal @=? output

    ,
      testCase "- NOT (NOT false)" $
      do output <- return $ 
           parse condition "" "NOT (NOT false)"
         expectVal <- return $
           Right $ CNot (CNot (CLit False))
         expectVal @=? output    
    ]
  ,
    testGroup "3) condition OR/AND condition"
    [  testCase "true AND false" $
       do output <- return $ 
            parse condition "" "true AND false"
          expectVal <- return $
            Right $ CAnd (CLit True) (CLit False)
          expectVal @=? output 
       
    ,   testCase "true OR false" $
       do output <- return $ 
            parse condition "" "true OR false"
          expectVal <- return $
            Right $ COr (CLit True) (CLit False) 
          expectVal @=? output
    ]
  ,
    testGroup "4) CHOICE (featureExpr,condition,condition)"
    [  testCase "- CHOICE(US, true, false)" $
       do output <- return $ 
            parse condition "" "CHOICE(US, true, false)"
          expectVal <- return $
            Right $ CChc (FRef (Feature {featureName = "US"})) 
                         (CLit True)
                         (CLit False)
          expectVal @=? output
    ]
    ,
    testGroup "test condition combination"
    [  testCase "- CHOICE(US, (price > 2000), (price > 1000)) AND count = 500" $
       do output <- return $ 
            parse condition "" "CHOICE(US, (price > 2000), (price > 1000)) AND count = 500"
          expectVal <- return $
            Right $ CAnd
                      ( CChc (FRef (Feature {featureName = "US"})) 
                          (CComp GT (Val (S "price")) (Val (I 2000)))
                          (CComp GT (Val (S "price")) (Val (I 1000))))
                      ( CComp EQ (Val (S "count")) (Val (I 500)))
          expectVal @=? output
    ]
  ]

--
-- ** test FromExpr /FROM relationlist
--

testFromExpr :: TestTree
testFromExpr = testGroup "Test FromExpr (FROM relationlist)"
  [  testGroup "1) FROM relation "
     [  testCase "- FROM encryption" $
        do output <- return $ 
             parse fromExpr "" "FROM encryption"
           expectVal <- return $
             Right $ From (R (Relation {relationName = "encryption"}))
           expectVal @=? output
    ]
  ,
    testGroup "2) FROM r1, r2, r3 .. "
    [  testCase "- FROM encryption, signature, referenceInfo" $
       do output <- return $ 
            parse fromExpr "" "FROM encryption, signature, referenceInfo"
          expectVal <- return $
            Right $ From (RelConcat 
                           (RelConcat 
                             (R (Relation {relationName = "encryption"}))  
                             (R (Relation {relationName = "signature"})) ) 
                           (R (Relation {relationName = "referenceInfo"}))) 
          expectVal @=? output   
    ]
  ,
    testGroup "3) FROM CHOICE(featureExpr, relationlist, relationlist)"
    [  testCase "FROM CHOICE(encrypt, encrption, signature)" $
       do output <- return $ 
            parse fromExpr "" "FROM CHOICE(encrypt, encrption)"
          expectVal <- return $
            Right $ From (Rel1Chc 
                           (FRef (Feature {featureName = "encrypt"}))
                           (R (Relation {relationName = "encrption"}))) 
          expectVal @=? output 
    ]
  -- ,
  --   testGroup "4) FROM nested choices"
  --   [  testCase "- FROM CHOICE(feature1, (CHOICE(feature2, relation2), relation1), relation1)" $
  --      do output <- return $ 
  --           parse fromExpr "" "FROM CHOICE(feature1, ( CHOICE(feature2, relation2) , relation1), relation1)"
  --         expectVal <- return $
  --           Right $ From (Rel2Chc (FRef (Feature {featureName = "feature1"})) 
  --                                 (RelConcat
  --                                  (Rel1Chc 
  --                                    (FRef (Feature {featureName = "feature2"}))
  --                                    (R (Relation {relationName = "relation2"})))
  --                                  (R (Relation {relationName = "relation1"})))
  --                                (R (Relation {relationName = "relation1"})))
  --         expectVal @=? output
  --   ]
  ]

--
-- ** test WhereExpr /WHERE condition
--




