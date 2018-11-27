module VDB.Example.EmployeeUseCase.EmployeeVSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Value
import VDB.Variational 

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.List(unionBy,nubBy)
import Data.Tuple(swap)

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

emptySchema :: Schema 
emptySchema = (Lit True, M.empty)  

-- | Merge a new schema to existing V-schema 
variationize :: Schema -> Schema -> Schema 
variationize s1@(lf,lm) s2@(rf,rm)  = let newf = lf `Or` rf 
                                          newRelMap = variationizeHelper s1 s2    
                                      in (newf, newRelMap)

-- | hselper function to get the Map of relation to optinal attribute list 
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
pushFeatureToRowType _ []     = []
pushFeatureToRowType f rowlist = map (\(_, attr) -> (f, attr)) rowlist

-- | Merge and update the featureExpr of two Rel Map
mergeRelMapFeatureExpr :: Map Relation (Opt RowType) -> Map Relation (Opt RowType) -> Map Relation (Opt RowType)
mergeRelMapFeatureExpr lRelMap rRelMap = M.unionWith unionRelFeatureExpr lRelMap rRelMap
-- mergeRelMapFeatureExpr lRelMap rRelMap = M.unionWith unionWithRelHelper lRelMap rRelMap

-- | Union FeatureExpr 
unionRelFeatureExpr :: (FeatureExpr, RowType) -> (FeatureExpr, RowType) -> (FeatureExpr, RowType)
unionRelFeatureExpr (Lit True, l)  (_, r)   = (Lit True  , unionRowType l r )
unionRelFeatureExpr (lf,l)         (rf,r)   = (lf `Or` rf, unionRowType l r )

-- | union Rowtype 
unionRowType :: RowType -> RowType -> RowType
unionRowType l r = let l' = M.fromList (map swap l)
                       r' = M.fromList (map swap r)
                   in  map swap (M.toList (M.unionWith unionRowtypeHelper l' r') ) 

-- | Helper function for unionRowtype 
unionRowtypeHelper :: FeatureExpr -> FeatureExpr ->   FeatureExpr
unionRowtypeHelper (Lit True)  _  = Lit True
unionRowtypeHelper lf         rf  = lf `Or` rf


--
-- * small test suite 
--

-- | small test for unionRelFeatureExpr 
-- testunionFeatureExpr :: Map Relation (FeatureExpr, RowType)
-- testunionFeatureExpr = M.unionWith unionWithRelHelper s1RelMap s2RelMap

-- testunionFeatureExpr2 :: Map Relation (FeatureExpr, RowType)
-- testunionFeatureExpr2 = M.unionWith unionWithRelHelper s1RelMap (pushFeatureToRelMap v2 s2RelMap)


-- | simple test case for variationize 
testS1 :: Schema 
testS1 = ( Ref "v1", s1RelMap)

s1RelMap :: Map Relation (Opt RowType)
s1RelMap = M.fromList [ (Relation "T1", (Lit True,  [ (Lit True, (Attribute "A1", TInt))
                                                    , (Lit True, (Attribute "A2", TString))]))]

testS2 :: Schema 
testS2 = ( Ref "v2", s2RelMap)


s2RelMap :: Map Relation (Opt RowType)
s2RelMap = M.fromList [ (Relation "T1", (Lit True,  [ (Lit True, (Attribute "A1", TInt))
                                                    , (Lit True, (Attribute "A3", TString))]))
                      , (Relation "T2", (Lit True,  [ (Lit True, (Attribute "A4", TInt))]))
                      ]

-- | my union for union rowtypes 
-- unionRowType :: [Opt (Attribute, Type)] -> [Opt (Attribute, Type)] -> [Opt (Attribute, Type)] 
-- unionRowType  xs ys = let xs' = map swap xs 
--                           ys' = map swap ys 
--                       in case 


rowtypes1 :: RowType
rowtypes1 =   [ (Lit True, (Attribute "A1", TInt)), (v1, (Attribute "A2", TString)), (v2, (Attribute "A3", TString))]

rowtypes2 :: RowType
rowtypes2 = [ (v3, (Attribute "A1", TInt)), (v3, (Attribute "A3", TString))]
 
-- instance Eq (Opt a) where

testRowtypes = [ (Lit True, (Attribute "A1", TInt)), (Lit True, (Attribute "A2", TString))]

l' = M.fromList (map swap rowtypes1)
r' = M.fromList (map swap rowtypes2)

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
