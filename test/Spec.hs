import Test.Tasty

import TypeSystem.Relational.Test0

import VDB.Schema.Variational.Test
-- import qualified Schema.Test as S

-- import TestParser 
-- import TestTranslater_Phase1
-- import TestTranslater_Phase2
-- import TestTwoOptionExample
-- import TestEmployeeSchema 
-- import TestEmployeeQuery

main :: IO ()
main = defaultMain $ testGroup "top level" 
  [ vschemaTests
  , trtypesys]

-- main = defaultMain $ testGroup ""
--         [ -- testTwoOptionExample
--         -- , testTransAlgebraToQuery
--         -- , testTranslater -- after editing syntax, all test case broken
--          testQualifyQuery
--         ,testEmployeeSchema
--         ,testEmployeeSelection
--         ,testEmployeeQuery
--         ]

  -- [ testFeatureExpr
  -- , testCondition
  -- , testFromExpr
  -- , testWhereExpr
  -- , testQueryExpr]