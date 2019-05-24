-- | Feature expression data type.
module VDBMS.Features.FeatureExpr.Types (

        FeatureExpr(..)

) where

import Data.Data (Data,Typeable)

import VDBMS.Features.Feature (Feature)


-- | Boolean expressions over features.
data FeatureExpr
   = Lit Bool
   | Ref Feature
   | Not FeatureExpr
   | And FeatureExpr FeatureExpr
   | Or  FeatureExpr FeatureExpr
  deriving (Data,Eq,Typeable,Ord)
