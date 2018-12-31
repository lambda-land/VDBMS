import Test.Tasty

import TestParser 
import TestTranslater_Phase1
import TestTranslater_Phase2
import TestTwoOptionExample
import TestEmployeeSchema 
import TestEmployeeQuery

main :: IO ()
main = defaultMain $ testGroup ""
        [ -- testTwoOptionExample
        -- , testTransAlgebraToQuery
        -- , testTranslater -- after editing syntax, all test case broken
         testEmployeeSchema
        ,testEmployeeSelection
        ,testEmployeeQuery
        ]

  -- [ testFeatureExpr
  -- , testCondition
  -- , testFromExpr
  -- , testWhereExpr
  -- , testQueryExpr]