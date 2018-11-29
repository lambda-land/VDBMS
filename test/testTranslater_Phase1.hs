module TestTranslater_Phase1 where 

import Test.Tasty
import Test.Tasty.HUnit

import VDB.Translations.VSqlToAlgebra
import VDB.SQL
import VDB.Algebra
import VDB.Name 
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import qualified VDB.Value as V

-- | Basic compolent for Queryies 
fA :: F.FeatureExpr 
fA = F.Ref (Feature "A")
fB = F.Ref (Feature "B")
fTrue = F.Lit True
fFalse = F.Lit False

attr1 :: Attribute
attr1 = Attribute "a1"
attr2 = Attribute "a2"

rel1 :: Relation 
rel1 = Relation "Table1"
rel2 = Relation "Table2"


testTranslater :: TestTree
testTranslater = testGroup "Test V-Query to V-Algebra"
  [  
    testGroup "1) No condition invovled"
    [  testCase "- SELECT [(Plain Attr)] FROM.. " $
       do output <- return $ 
            vsqlToAlgebra $ VSelect [(fTrue, attr1), (fTrue, attr2)] [(fTrue, rel1)] Nothing
          expectVal <- return $ Proj [(fTrue, attr1), (fTrue, attr2)] 
                                      (SetOp Prod (TRef rel1) Empty)
          expectVal @=? output
    ,  testCase "- SELECT [Attr with Tag] FROM ..." $
       do output <- return $ 
            vsqlToAlgebra $ VSelect [(fA, attr1), (fB, attr2)] 
                                    [(fTrue, rel1)] Nothing
          expectVal <- return $ Proj [(fA, attr1), (fB, attr2)] 
                                     (SetOp Prod (TRef rel1) Empty)
          expectVal @=? output
    ,  testCase "- SELECT [Attr with Tag] FROM [Rel with Tag]" $
       do output <- return $ 
            vsqlToAlgebra $ VSelect [(fA, attr1), (fB, attr2)] 
                                    [(fA, rel1)] Nothing
          expectVal <- return $ Proj [(fA, attr1), (fB, attr2)] 
                                     (SetOp Prod (AChc fA (TRef rel1) Empty) Empty)
          expectVal @=? output
    -- , testCase "- SELECT ... FROM [Rel with Tag]" $
    --    do output <- return $ 
    --         vsqlToAlgebra $  VSelect [(fA, attr1), (fB, attr2)] 
    --                                  [(fA, rel1),(fB, rel2)] 
    --                                  Nothing
    --       expectVal <- return $ Proj [(fA, attr1), (fB, attr2)] 
    --                                  (SetOp Prod (AChc fA (TRef rel1) Empty) ((SetOp Prod (AChc fA (TRef rel2) Empty) (Empty))))
          -- expectVal @=? output
    ]
    ,
     testGroup "2) Condition Involved"
    [  testCase "- SELECT.. FROM.. WHERE attr1 > 5" $
        do output <- return $ 
              vsqlToAlgebra $  VSelect [(fA, attr1), (fB, attr2)] 
                               [(fA, rel1)] 
                               (Just (C.Comp V.GT (C.Attr attr1) (C.Val (V.I 5))) )   

           expectVal <- return $ Proj [(fA, attr1), (fB, attr2)] 
                                 $ Sel (C.Comp V.GT (C.Attr attr1) (C.Val (V.I 5))) 
                                 (SetOp Prod (AChc fA (TRef rel1) Empty) Empty)
  
            
           expectVal @=? output
    ]

  ]

  -- Proj [(A,Attribute {attributeName = "a1"}),(B,Attribute {attributeName = "a2"})] (Sel (Comp GT (Attr (Attribute {attributeName = "a1"})) (Val (I 5))) (SetOp Prod (AChc A (TRef (Relation {relationName = "Table1"})) Empty) Empty))




  
  
