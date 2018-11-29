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
import VDB.Translations.AlgebraToSql


import Data.Map(Map)
import qualified Data.Map as Map 

import Data.Set (Set)
import qualified Data.Set as Set

-- | Basic compolent for Queryies and Algebra 

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
-- 
--  ** test transAlgebraToQuery
-- 

testTransAlgebraToQuery :: TestTree
testTransAlgebraToQuery = testGroup "Test transAlgebraToQuery"
  [
    testGroup "1) just projection"
    [  testCase "- Proj a1,a2 (Table1)" $
       do output <- return $ transAlgebraToQuery (  
            Proj [(fTrue, 
                   attr1)
               ,(fTrue,
                   attr2)
               ] 
            (TRef (rel1)) )
          expectVal <- return $
            Select [attr1, attr2] 
            (Where Nothing (From (rel1)))
          expectVal @=? output
    ]
  , testGroup "2) projection with selection"
    [  testCase "- Proj a1,a2 (Table1)" $
       do output <- return $ transAlgebraToQuery $
            Proj [(fTrue, attr1)] $ 
            Sel (C.Comp GT 
                  (C.Attr (attr1)) 
                  (C.Val (I 5))) $ 
            (TRef (rel2))
          expectVal <- return $
            Select [attr1] 
            (Where (Just (And (T.SAT (fFalse )) (Comp GT (C.Attr (attr1)) (C.Val (I 5))))) 
            (From (rel2)))

          expectVal @=? output
    ]
    , testGroup "3) have variational condition  "
    [  testCase "- Proj a1 Sel A(a1 > 5, a1 < 5) (Table1)" $ 
       do output <- return $ transAlgebraToQuery $
            Proj [(fTrue, attr1)] $ 
            Sel (C.CChc (fA) 
                       (C.Comp GT (C.Attr a1) (C.Val (I 5))) 
                       (C.Comp LT (C.Attr a1) (C.Val (I 5)))) $ 
            (TRef (rel2))
          expectVal <- return $ 
            Select [attr1] 
            (QueryOp Union 
              (Where (Just (And (T.SAT (fFalse )) 
                                (And (Comp GT (C.Attr (Attribute "course")) (C.Val (I 5))) 
                                     (T.SAT (fA)) ))) 
                (From (rel2))) 
              (Where (Just (And (T.SAT (fFalse ))  
                                (And (Comp LT (C.Attr (Attribute "course")) (C.Val (I 5))) 
                                    (T.SAT (F.Not (fA))) ))) 
                (From (rel2))))

          expectVal @=? output
    ]
    , testGroup "4) variational query "
    [  testCase "- A<Proj a1 (Table1), Proj a2 (Table2)>" $ 
       do output <- return $ transAlgebraToQuery $
            AChc (fA) 
             (Proj [(fTrue, attr1)] (TRef (rel2))) 
             (Proj [(fTrue, attr1)] (TRef (rel2)))
          expectVal <- return $
            QueryOp Union 
              (Select [attr1] 
                (Where (Just (And (T.SAT (fFalse ))   (T.SAT (fA)) ))  
                  (From (rel2)))) 
              (Select [attr1] 
                (Where (Just (And (T.SAT (fFalse ))   
                                  (T.SAT (F.Not (fA))) ))   
                (From (rel2)) ))
          expectVal @=? output
    ]


  ]


