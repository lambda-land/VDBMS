module Example.EmployeeUseCase.EmployeeVSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type
import VDB.Variational 
import Example.EmployeeUseCase.EmployeeSchema

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.List(unionBy,nubBy)
import Data.Tuple(swap)

import Database.HDBC (SqlValue)
import Data.SBV

-- | FeatureExpr for 5 schema version

empv1,empv2,empv3,empv4,empv5 :: FeatureExpr
empv1 = Ref (Feature "v1")
empv2 = Ref (Feature "v2")
empv3 = Ref (Feature "v3")
empv4 = Ref (Feature "v4")
empv5 = Ref (Feature "v5")

-- | Gaven a list of feature Expr, fold it into a Feature Model (TO DO)
-- buildFeatureModel :: [FeatureExpr] -> FeatureExpr
-- buildFeatureModel []     = Lit False 
-- buildFeatureModel (x:xs) = 

-- | Feature Model of Employee Schema 
-- employeeFeatureModel :: FeatureExpr
-- employeeFeatureModel =  (v1 `And` (Not v2) `And` (Not v3) `And` (Not v4) `And` (Not v5)) `Or` 
--                         ((Not v1) `And` v2 `And` (Not v3) `And` (Not v4) `And` (Not v5)) `Or` 
--                         ((Not v1) `And` (Not v2) `And` v3`And` (Not v4) `And` (Not v5)) `Or` 
--                         ((Not v1) `And` (Not v2) `And` (Not v3) `And` v4 `And` (Not v5)) `Or` 
--                         ((Not v1) `And` (Not v2) `And` (Not v3) `And` (Not v4) `And` v5)  



{-
((((((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR 
(NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND NOT v4) OR 
(NOT ((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR 
(NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND v4)) AND NOT v5) OR 
(NOT ((((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR 
(NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND NOT v4) OR 
(NOT ((((v1 AND NOT v2) OR (NOT v1 AND v2)) AND NOT v3) OR 
(NOT ((v1 AND NOT v2) OR (NOT v1 AND v2)) AND v3)) AND v4)) AND v5),
fromList [
(Relation {relationName = "v_dept"},
((v3 OR v4) OR v5,
fromList [(Attribute {attributeQualifier = Just (Relation {relationName = "v_dept"}), 
attributeName = "deptname"},((v3 OR v4) OR v5,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_dept"}), 
attributeName = "deptno"},((v3 OR v4) OR v5,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_dept"}), 
attributeName = "managerno"},((v3 OR v4) OR v5,TInt32))])),
(Relation {relationName = "v_empacct"},(((v2 OR v3) OR v4) OR v5,
fromList [(Attribute {attributeQualifier = Just (Relation {relationName = "v_empacct"}), 
attributeName = "deptname"},(v2,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empacct"}), 
attributeName = "deptno"},((v3 OR v4) OR v5,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empacct"}), 
attributeName = "empno"},(((v2 OR v3) OR v4) OR v5,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empacct"}), 
attributeName = "hiredate"},(((v2 OR v3) OR v4) OR v5,TUTCTime)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empacct"}), 
attributeName = "name"},(v2 OR v3,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empacct"}), 
attributeName = "salary"},(v5,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empacct"}), 
attributeName = "title"},(((v2 OR v3) OR v4) OR v5,TString))])),
(Relation {relationName = "v_empbio"},(v4 OR v5,
fromList [(Attribute {attributeQualifier = Just (Relation {relationName = "v_empbio"}), 
attributeName = "birthdate"},(v4 OR v5,TUTCTime)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empbio"}), 
attributeName = "empno"},(v4 OR v5,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empbio"}), 
attributeName = "firstname"},(v5,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empbio"}), 
attributeName = "lastname"},(v5,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empbio"}), 
attributeName = "name"},(v4,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_empbio"}), 
attributeName = "sex"},(v4 OR v5,TString))])),
(Relation {relationName = "v_engineerpersonnel"},
(v1,fromList [(Attribute {attributeQualifier = Just (Relation {relationName = "v_engineerpersonnel"}), 
attributeName = "deptname"},(v1,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_engineerpersonnel"}), 
attributeName = "empno"},(v1,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_engineerpersonnel"}), 
attributeName = "hiredate"},(v1,TUTCTime)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_engineerpersonnel"}), 
attributeName = "name"},(v1,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_engineerpersonnel"}), 
attributeName = "title"},(v1,TString))])),(Relation {relationName = "v_job"},(((v1 OR v2) OR v3) OR v4,
fromList [(Attribute {attributeQualifier = Just (Relation {relationName = "v_job"}), 
attributeName = "salary"},(((v1 OR v2) OR v3) OR v4,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_job"}), 
attributeName = "title"},(((v1 OR v2) OR v3) OR v4,TString))])),
(Relation {relationName = "v_otherpersonnel"},
(v1,fromList [(Attribute {attributeQualifier = Just (Relation {relationName = "v_otherpersonnel"}), 
attributeName = "deptname"},(v1,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_otherpersonnel"}), 
attributeName = "empno"},(v1,TInt32)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_otherpersonnel"}), 
attributeName = "hiredate"},(v1,TUTCTime)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_otherpersonnel"}), 
attributeName = "name"},(v1,TString)),
(Attribute {attributeQualifier = Just (Relation {relationName = "v_otherpersonnel"}), 
attributeName = "title"},(v1,TString))]))])
-}



-- | fold a list of schema into one variational schema 
variationizeSchema :: [Schema] -> Schema
variationizeSchema = foldl variationize' emptySchema 

-- | starting schmea for variationize
emptySchema :: Schema 
emptySchema = (Lit False, M.empty)   

-- | Merge a new schema to existing V-schema 
variationize' :: Schema -> Schema -> Schema 
variationize' s1@(lf,lm) s2@(rf,rm)  = let newf = shrinkFeatureExpr (lf <+> rf) 
                                           newRelMap = variationizeHelper s1 s2    
                                       in (newf, newRelMap)

-- | helper function to get the Map of relation to optional attribute list 
variationizeHelper :: Schema -> Schema ->  Map Relation (Opt RowType)
variationizeHelper s1@(lf,lm) s2@(rf,rm) = case M.toList lm of 
                                            []     -> (pushFeatureToRelMap rf rm) 
                                            relMap -> let rm' = pushFeatureToRelMap rf rm  
                                                      in mergeRelMapFeatureExpr lm rm'

-- | simplely pushdown the * featureExpr * to the Relation and Attributes(RowType)
pushFeatureToRelMap :: FeatureExpr -> Map Relation (Opt RowType) -> Map Relation (Opt RowType)
pushFeatureToRelMap f relMap  = case M.toList relMap of 
                                        []     -> M.fromList [] 
                                        rlist ->  M.fromList $ map (\(rel, (rf, rows)) -> (rel, (f, pushFeatureToRowType f rows) )) rlist 

-- | push the gaven FeatureExpr to rowtype 
pushFeatureToRowType :: FeatureExpr -> RowType -> RowType
pushFeatureToRowType f rt = case M.toList rt of 
                             [] -> M.empty
                             _  -> M.map (\(_, t) -> (f, t)) rt

-- | Merge and update the featureExpr of two Rel Map
mergeRelMapFeatureExpr :: Map Relation (Opt RowType) -> Map Relation (Opt RowType) -> Map Relation (Opt RowType)
mergeRelMapFeatureExpr lRelMap rRelMap = M.unionWith unionRelFeatureExpr lRelMap rRelMap

-- | Union FeatureExpr 
unionRelFeatureExpr :: (FeatureExpr, RowType) -> (FeatureExpr, RowType) -> (FeatureExpr, RowType)
unionRelFeatureExpr (lf,l)         (rf,r)   = (shrinkFeatureExpr (lf `Or` rf), unionRowType l r )


-- | union Rowtype 
unionRowType :: RowType -> RowType -> RowType
unionRowType = M.unionWith unionRowtypeHelper
                  -- where unionRowtypeHelper (f1, t1) (f2, r2)  = (shrinkFeatureExpr (lf `Or` rf)


-- | Helper function for unionRowtype  
--   
unionRowtypeHelper :: Opt SqlType -> Opt SqlType -> Opt SqlType
unionRowtypeHelper (lf,l)         (rf,r) = (shrinkFeatureExpr (lf `Or` rf), l)




--
-- * small test suite 
--

-- | small test for unionRelFeatureExpr 
-- testunionFeatureExpr :: Map Relation (FeatureExpr, RowType)
-- testunionFeatureExpr = M.unionWith unionWithRelHelper s1RelMap s2RelMap

-- testunionFeatureExpr2 :: Map Relation (FeatureExpr, RowType)
-- testunionFeatureExpr2 = M.unionWith unionWithRelHelper s1RelMap (pushFeatureToRelMap v2 s2RelMap)


-- | simple test case for variationize 
 -- s1^v1 = {T1(A1,A2)}
-- testS1 :: Schema 
-- testS1 = ( v1, s1RelMap)

-- s1RelMap :: Map Relation (Opt RowType)
-- s1RelMap = constructRelMap [ ("T1",  [ ("A1",  TInt32), ("A2", TString)])]
-- -- s2^v2 = {T1(A1,A3,A4), T2(A4)}
-- testS2 :: Schema 
-- testS2 = ( v2, s2RelMap)


-- s2RelMap :: Map Relation (Opt RowType)
-- s2RelMap = constructRelMap [ ("T1",  [ ("A1",  TInt32), ( "A3",  TString)])
--                            , ( "T2", [ ("A4", TInt32)])
--                            ]

-- testS3 :: Schema
-- testS3 = (v3, s3RelMap)

-- s3RelMap :: Map Relation (Opt RowType)
-- s3RelMap = M.fromList [ (Relation "T3", (Lit True,  [ (Lit True, (Attribute "A5", TInt32))]))
--                       ]


-- shrinkF  = shrinkFeatureExpr (Or (Lit False) (v2))

-- | my union for union rowtypes 
-- unionRowType :: [Opt (Attribute, Type)] -> [Opt (Attribute, Type)] -> [Opt (Attribute, Type)] 
-- unionRowType  xs ys = let xs' = map swap xs 
--                           ys' = map swap ys 
--                       in case 


-- rowtypes1 :: RowType
-- rowtypes1 =   [ (Lit True, (Attribute "A1", TInt32)), (v1, (Attribute "A2", TString)), (v2, (Attribute "A3", TString))]

-- rowtypes2 :: RowType
-- rowtypes2 = [ (v3, (Attribute "A1", TInt32)), (v3, (Attribute "A3", TString))]
 
-- -- instance Eq (Opt a) where

-- testRowtypes = [ (Lit True, (Attribute "A1", TInt32)), (Lit True, (Attribute "A2", TString))]

-- l' = M.fromList (map swap rowtypes1)
-- r' = M.fromList (map swap rowtypes2)

-- testlr = M.unionWith unionRowtypesFeatureExpr l' r'
-- testlr = map swap (M.toList (M.unionWith unionRowtypesFeatureExpr l' r') ) 



-- | comment out funtion

-- | Union FeatureExpr 
-- unionWithRelHelper :: (FeatureExpr, RowType) -> (FeatureExpr, RowType) -> (FeatureExpr, RowType)
-- unionWithRelHelper (Lit True, l)  (_, r)   = (Lit True  , unionBy unionByRowTypesHelper l r)
-- unionWithRelHelper (lf,l)         (rf,r)   = (lf `Or` rf, unionBy unionByRowTypesHelper l r ) 
-- | Union RowTypes 
-- unionByRowTypesHelper :: Opt (Attribute, Type)-> Opt (Attribute, Type) -> Bool
-- unionByRowTypesHelper = undefined 
