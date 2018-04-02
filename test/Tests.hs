module Main where

import Test.Tasty

import TestParser 

main :: IO ()
main = defaultMain $ testGroup ""
  [ testFeatureExpr
  , testCondition
  , testFromExpr
  , testQueryExpr]