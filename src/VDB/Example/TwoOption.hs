module VDB.Example.TwoOption where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Value 

import qualified Data.Map as Map 


-- | a table with 2 feature expresion a and b invovled
tableWithTwoOption :: RowType 
tableWithTwoOption = [ ( Lit False,                          (Attribute "a1", TInt))
                     , ( And a b,                            (Attribute "a2", TInt))
                     , ( And a (Not b),                      (Attribute "a3", TInt))
                     , ( a,                                  (Attribute "a4", TInt))
                     , ( And (Not a) b,                      (Attribute "a5", TInt))
                     , ( b,                                  (Attribute "a6", TInt))
                     , ( Or (And (Not a) b) (And a (Not b)), (Attribute "a7", TInt))
                     , ( Or a b,                             (Attribute "a8", TInt))
                     , ( And (Not a) (Not b),                (Attribute "a9", TInt))
                     , ( Or (And (Not a) (Not b)) (And a b), (Attribute "a10", TInt))
                     , ( Not b,                              (Attribute "a11", TInt))
                     , ( Or (Not b) a,                       (Attribute "a12", TInt))
                     , ( Not a,                              (Attribute "a13", TInt))
                     , ( Or (Not a) b ,                      (Attribute "a14", TInt))
                     , ( Or (Not a) (Not b),                 (Attribute "a15", TInt))
                     , ( Lit True,                           (Attribute "a16", TInt))]

schemaEg1 = (Lit True, Map.fromList [((Relation "t1"), (Lit True, tableWithTwoOption))] )
-- | "a"/"b" is a feature expression refrencing feature "A"/"B"
a :: FeatureExpr
a = Ref (Feature "A")

b :: FeatureExpr
b = Ref (Feature "B")



