import Test.Tasty

import TestParser 
import TestTranslater_Phase1
import TestTranslater_Phase2
import TestTwoOptionExample

main :: IO ()
main = defaultMain $ testGroup ""
        [ testTwoOptionExample
        , testTransAlgebraToQuery
        , testTranslater -- after editing syntax, all test case broken
        -- , testEmployee
        ]

  -- [ testFeatureExpr
  -- , testCondition
  -- , testFromExpr
  -- , testWhereExpr
  -- , testQueryExpr]