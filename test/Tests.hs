module Main where

import Test.Tasty

import TestParser 
import TestTranslater

main :: IO ()
main = defaultMain $ testGroup ""
         [testTranslater]
  -- [ testFeatureExpr
  -- , testCondition
  -- , testFromExpr
  -- , testWhereExpr
  -- , testQueryExpr]