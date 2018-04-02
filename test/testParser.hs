module TestParser where 

import Test.Tasty
import Test.Tasty.HUnit

import Text.Megaparsec
-- import Control.Monad.Identity 

import VDB.ParsingSQL


-- testFeatureExpr :: TestTree 
-- testFeatureExpr = testGroup ""
-- parse :: Stream s Identity t => Parser a -> SourceName -> s -> Either ParseError a
-- main = case (parse condition "" "true") of
--             Left err  -> print err
--             Right xs  -> print xs
-- main :: IO ()
-- main = defaultMain $ testGroup ""
--   [testFeatureExpr]

-- | ** Helper function
-- roundTrip ::(Eq a, Show a) => String -> a -> Parser a -> String -> Assertion
-- roundTrip name input parser = 
--   case (parse parser "" input) of 
--     Right res -> assertEqual ("roundTrip " ++ name ) input res 
--     Left err  -> do
--       putStrLn "Error Parsing SQL:"
--       printParseError err
--       assertFailure ("roudnTrip parse error: " ++ name) 

-- parseFeatureExpr :: (Show a) =>  Parser a -> String -> IO ()
-- parseFeatureExpr parser input = parseTest parser input

testFeatureExpr :: TestTree
testFeatureExpr = testCase "test featureExpr" 
  (assertEqual "False =? false " (Right $ FLit False) (parse featureExpr "" "false"))
        
--         -- do out <- parse featureExpr "" "true"
--         --   let expect = FLit True 
--         --   out @?= expect 
       
--         testCase "FeatureExpr of Bool" $
--          do let expect = FLit False 
--             roundTrip "2" expect featureExpr "false"
--        ]