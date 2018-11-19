module VDB.Example.EmployeeUseCase.EmployeeQuery where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Value 

import qualified Data.Map as Map 

-- | FeatureExpr for 5 schema version
v1,v2,v3,v4,v5 :: FeatureExpr
v1 = Ref (Feature "v1")
v2 = Ref (Feature "v2")
v3 = Ref (Feature "v3")
v4 = Ref (Feature "v4")
v5 = Ref (Feature "v5")


-- | Gaven a list of feature Expr, fold it into a Feature Model (TO DO)
-- buildFeatureModel :: [FeatureExpr] -> FeatureExpr
-- buildFeatureModel []     = Lit False 
-- buildFeatureModel (x:xs) = 

-- | Feature Model of Employee Schema 
employeeFeatureModel :: FeatureExpr
employeeFeatureModel =  (v1 `And` (Not v2) `And` (Not v3) `And` (Not v4) `And` (Not v5)) `Or` 
                        ((Not v1) `And` v2 `And` (Not v3) `And` (Not v4) `And` (Not v5)) `Or` 
                        ((Not v1) `And` (Not v2) `And` v3`And` (Not v4) `And` (Not v5)) `Or` 
                        ((Not v1) `And` (Not v2) `And` (Not v3) `And` v4 `And` (Not v5)) `Or` 
                        ((Not v1) `And` (Not v2) `And` (Not v3) `And` (Not v4) `And` v5)  

      