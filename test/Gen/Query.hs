module Gen.Query where

import qualified Test.Tasty.QuickCheck as Q
import Control.Monad (liftM,liftM2)

import VDB.Algebra
import VDB.FeatureExpr
import VDB.Name
import VDB.SAT

-- | Generate only alphabetical characters
genAlphaNum :: Q.Gen String
genAlphaNum = pure <$> Q.elements ['a'..'z']

-- | generate a list of only alphabetical characters and convert to Dim
genAlphaNumStr :: Q.Gen String
genAlphaNumStr = fmap mconcat $ 
  flip Q.suchThat (not . null) $ Q.listOf genAlphaNum

-- | generate a feature expression, Lit <$> Q.arb == Q.arb >>= return .Lit
genFeatureExpr :: Int -> [Feature] -> Q.Gen FeatureExpr
genFeatureExpr n fs = Q.oneof 
  [ Lit <$> Q.arbitrary
  , liftM Ref $ genFeature fs
  , liftM  Not l
  , liftM2 And l l
  , liftM2 Or  l l
  ]
  where l = genFeatureExpr (n `div` 2) fs

-- | Given a list of features generate a feature randomly from the list
genFeature :: [Feature] -> Q.Gen Feature
genFeature = Q.elements

-- |
isAppFMNotFalse :: FeatureExpr -> FeatureExpr -> Bool
isAppFMNotFalse = (satisfiable .) . And

-- isAppFMNotFalse f fm = satisfiable $ And f fm

-- TO RUN IN GHCI: stack ghci vdbms:vdbms-test
