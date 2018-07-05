module Main where

import Test.Tasty

import TestParser 
import TestTranslater_Phase1
import TestTranslater_Phase2

main :: IO ()
main = defaultMain $ testGroup ""
        [testTransAlgebraToQuery]
         -- [ testTranslater_Phase1
         -- , testTranslater_Phase2]
  -- [ testFeatureExpr
  -- , testCondition
  -- , testFromExpr
  -- , testWhereExpr
  -- , testQueryExpr]