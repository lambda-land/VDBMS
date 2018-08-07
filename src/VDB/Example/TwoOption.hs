module VDB.Example.TwoOption where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Value 


-- | a table with 2 feature expresion invovled
tableWithTWoOption :: RowType 
tableWithTWoOption = [ ( Lit False,                          (Attribute {attributeName = "a1"}, TInt))
                     , ( And a b,                            (Attribute {attributeName = "a2"}, TInt))
                     , ( And a (Not b),                      (Attribute {attributeName = "a3"}, TInt))
                     , ( a,                                  (Attribute {attributeName = "a4"}, TInt))
                     , ( And (Not a) b,                      (Attribute {attributeName = "a5"}, TInt))
                     , ( b,                                  (Attribute {attributeName = "a6"}, TInt))
                     , ( Or (And (Not a) b) (And a (Not b)), (Attribute {attributeName = "a7"}, TInt))
                     , ( Or a b,                             (Attribute {attributeName = "a8"}, TInt))
                     , ( And (Not a) (Not b),                (Attribute {attributeName = "a9"}, TInt))
                     , ( Or (And (Not a) (Not b)) (And a b), (Attribute {attributeName = "a10"}, TInt))
                     , ( Not b,                              (Attribute {attributeName = "a11"}, TInt))
                     , ( Or (Not b) a,                       (Attribute {attributeName = "a12"}, TInt))
                     , ( Not a,                              (Attribute {attributeName = "a13"}, TInt))
                     , ( Or (Not a) b ,                      (Attribute {attributeName = "a14"}, TInt))
                     , ( Or (Not a) (Not b),                 (Attribute {attributeName = "a15"}, TInt))
                     , ( Lit True,                           (Attribute {attributeName = "a16"}, TInt))]

-- | "a"/"b" is a feature expression refrencing feature "A"/"B"
a :: FeatureExpr
a = (Ref (Feature {featureName = "A"}))

b :: FeatureExpr
b = (Ref (Feature {featureName = "B"}))



