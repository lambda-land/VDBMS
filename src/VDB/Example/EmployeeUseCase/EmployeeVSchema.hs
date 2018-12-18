module VDB.Example.EmployeeUseCase.EmployeeVSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type
import VDB.Variational 
import VDB.Example.EmployeeUseCase.EmployeeSchema

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.List(unionBy,nubBy)
import Data.Tuple(swap)

import Database.HDBC (SqlValue)
import Data.SBV

-- | FeatureExpr for 5 schema version
v1,v2,v3,v4,v5 :: FeatureExpr
v1 = Ref (Feature "v1")
v2 = Ref (Feature "v2")
v3 = Ref (Feature "v3")
v4 = Ref (Feature "v4")
v5 = Ref (Feature "v5")


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
testS1 :: Schema 
testS1 = ( v1, s1RelMap)

s1RelMap :: Map Relation (Opt RowType)
s1RelMap = constructRelMap [ ("T1",  constructRowType [ ("A1",  TInt32), ("A2", TString)])]
-- s2^v2 = {T1(A1,A3,A4), T2(A4)}
testS2 :: Schema 
testS2 = ( v2, s2RelMap)


s2RelMap :: Map Relation (Opt RowType)
s2RelMap = constructRelMap [ ("T1", constructRowType [ ("A1",  TInt32), ( "A3",  TString)])
                           , ( "T2",constructRowType [ ("A4", TInt32)])
                           ]

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
