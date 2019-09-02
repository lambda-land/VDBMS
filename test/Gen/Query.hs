module Gen.Query where

import qualified Test.Tasty.QuickCheck as Q
import Control.Monad (liftM,liftM2)

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import VDBMS.Features.SAT

-- | Generate only alphabetical characters
genAlphaNum :: Q.Gen String
genAlphaNum = pure <$> Q.elements ['a'..'z']

-- | generate a list of only alphabetical characters and convert to Dim
genAlphaNumStr :: Q.Gen String
genAlphaNumStr = fmap mconcat $ 
  flip Q.suchThat (not . null) $ Q.listOf genAlphaNum

-- | generate a feature expression, Lit <$> Q.arb == Q.arb >>= return .Lit
genFeatureExpr :: Int -> [F.Feature] -> Q.Gen F.FeatureExpr
genFeatureExpr n fs = Q.oneof 
  [ F.Lit <$> Q.arbitrary
  , liftM F.Ref $ genFeature fs
  , liftM  F.Not l
  , liftM2 F.And l l
  , liftM2 F.Or  l l
  ]
  where l = genFeatureExpr (n `div` 2) fs

-- | Given a list of features generate a feature randomly from the list
genFeature :: [F.Feature] -> Q.Gen F.Feature
genFeature = Q.elements

-- |
isAppFMNotFalse :: F.FeatureExpr -> F.FeatureExpr -> Bool
isAppFMNotFalse = (satisfiable .) . F.And

-- isAppFMNotFalse f fm = satisfiable $ And f fm

-- TO RUN IN GHCI: stack ghci vdbms:vdbms-test
