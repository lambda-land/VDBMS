module TestTranslater where 

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

testTranslater :: TestTree
testTranslater = testGroup "Test V-Query to V-Algebra"
  [  
    testGroup "1) No condition invovled"
    [  testCase "- SELECT.. FROM.. " $
        do output <- return $ 

             vsqlToAlgebra $ (Select [((F.And 
                                        (F.Ref (Feature { featureName = "A" }) )  
                                        (F.Ref (Feature { featureName = "A" }) )), (Attribute { attributeName = "1" }))
                                    , 
                                     ((F.Ref (Feature { featureName = "B" })), (Attribute { attributeName = "2" }))
                                    ] 
                                    [((F.Ref (Feature { featureName=" B" })),(Relation { relationName = "1" }))
                                    , 
                                     ((F.Ref (Feature { featureName = "C" })),( Relation { relationName = "2" }))
                                    ]) 
                                    Nothing
           expectVal <- return $
            Proj [(F.And 
                    (F.Ref (Feature {featureName = "A"})) 
                    (F.Ref (Feature {featureName = "A"})), 
                   Attribute {attributeName = "1"})
                 ,
                  (F.Ref (Feature {featureName = "B"}),
                   Attribute {attributeName = "2"})
                 ] 
                  (SetOp Prod 
                        (AChc (F.Ref (Feature {featureName = " B"})) 
                              (TRef (Relation {relationName = "1"})) 
                               Empty) 
                        (SetOp Prod 
                              (AChc (F.Ref (Feature {featureName = "C"})) 
                                    (TRef (Relation {relationName = "2"})) 
                                     Empty) 
                               Empty))
           expectVal @=? output
    ]
    ,
     testGroup "2) Condition Involved"
    [  testCase "- SELECT.. FROM.. WHERE isEncrypted = true" $
        do output <- return $ 
              vsqlToAlgebra $  Select [ ( (F.Lit True), (Attribute {attributeName = "mid"}) ), 
                                   (  (F.Ref (Feature {featureName = "encrypt"})) ,(Attribute {attributeName = "isEncrypted"})),
                                   ((F.Lit True),(Attribute {attributeName = "mid"}))
                                  ]
                                  [ ( (F.Lit True) ,(Relation {relationName = "encryption"}))
                                  ]
                                  (Just (Comp V.EQ (Val (V.S "isEncrypted")) (Val (V.B True))) )     

           expectVal <- return $
                     Proj [ ((F.Lit True),(Attribute {attributeName = "mid"})), 
                   ( (F.Ref (Feature {featureName = "encrypt"})) ,(Attribute {attributeName = "isEncrypted"})),
                   ((F.Lit True), (Attribute {attributeName = "mid"}))
                 ]
                 $ Sel (Comp V.EQ (Val (V.S "isEncrypted")) (Val (V.B True))) 
                      (SetOp Prod (TRef (Relation {relationName = "encryption"})) Empty)
  
            
           expectVal @=? output
    ]

  ]




  
  
