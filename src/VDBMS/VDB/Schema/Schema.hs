-- | Variational database schemas.
module VDBMS.VDB.Schema.Schema (

        module VDBMS.VDB.Schema.Types,
        module VDBMS.VDB.Schema.Lookups,
        module VDBMS.VDB.Schema.Core,
        module VDBMS.VDB.Schema.ApplyConf,
        module VDBMS.VDB.Schema.ApplyFexp,
        module VDBMS.VDB.Schema.Equiv

) where

import VDBMS.VDB.Schema.Types
import VDBMS.VDB.Schema.Lookups 
import VDBMS.VDB.Schema.Core
import VDBMS.VDB.Schema.ApplyConf
import VDBMS.VDB.Schema.ApplyFexp
import VDBMS.VDB.Schema.Equiv

------------------ constructing schema -------------------
--  taken from:
--  VDBMS/src/VDB/Example/EmployeeUseCase/EmployeeVSchema.hs.
--  by Qiaoran
{-
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
variationizeHelper :: Schema -> Schema ->  Map Relation (TableSchema)
variationizeHelper s1@(lf,lm) s2@(rf,rm) = case M.toList lm of 
                                            []     -> (pushFeatureToRelMap rf rm) 
                                            relMap -> let rm' = pushFeatureToRelMap rf rm  
                                                      in mergeRelMapFeatureExpr lm rm'

-- | simplely pushdown the * featureExpr * to the Relation and Attributes(RowType)
pushFeatureToRelMap :: FeatureExpr -> Map Relation (TableSchema) -> Map Relation (TableSchema)
pushFeatureToRelMap f relMap  = case M.toList relMap of 
                                        []     -> M.fromList [] 
                                        rlist ->  M.fromList $ map (\(rel, (rf, rows)) -> (rel, (f, pushFeatureToRowType f rows) )) rlist 

-- | push the gaven FeatureExpr to rowtype 
pushFeatureToRowType :: FeatureExpr -> RowType -> RowType
pushFeatureToRowType f rt = case M.toList rt of 
                             [] -> M.empty
                             _  -> M.map (\(_, t) -> (f, t)) rt

-- | Merge and update the featureExpr of two Rel Map
mergeRelMapFeatureExpr :: Map Relation (TableSchema) -> Map Relation (TableSchema) -> Map Relation (TableSchema)
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
-}

-- | Get all info of an attribute from a rowtype
--lookupAttInRel :: Attribute -> Relation -> Schema -> Maybe (Opt (Attribute,Type))
--lookupAttInRel a r s = case lookupRowType r s of
--                         Just (f,m) -> retrieve m a 
--                         _ -> Nothing

-- | lookup an attribute of a specific relation in database
--lookupAtt :: Attribute -> Relation -> Schema -> Maybe (Opt (Attribute,Type))
--lookupAtt a r s = case lookupRowType r s of 
--                    Just (f,l) -> lookupAttInRel a r s
--                    Just (o,(a,t))
--                    _ -> Nothing


-- | Lookup b in Map (a,b) v.
-- lookupSnd :: Eq b => b -> Map (a,b) c -> Maybe c
-- lookupSnd att M.fromLi(((id,att'),ft):ys) = if att == att' then (Just ft) else lookupSnd att (M.fromList ys)
-- lookupSnd _ empty = Nothing


-- | Get the type and feature exp of a unique attribute in a database.
--lookupUniqueAttribute :: UniqeAttribute -> Relation -> Schema -> Maybe (Opt Type)
--lookupUniqueAttribute ua r s = case lookupRelationSchema r s of 
--                                Just (_,rs) -> M.lookup ua rs
--                                _ -> Nothing


-- | Get the type and feature exp of an attribute in a database.
--lookupAttribute :: Attribute -> Relation -> Schema -> Maybe (Opt Type)
--lookupAttribute a r s = case lookupRelationSchema r s of 
--                          Just (_,rs) -> lookupSnd a rs
--                          _ -> Nothing



{-- | Get the type of an attribute in the database
lookupAttPresCond :: Attribute -> Relation -> Schema -> Maybe FeatureExpr
lookupAttPresCond a r s = case lookupAtt a r s of
                            Just (f,_) -> Just f
                            _ -> Nothing
--}
