-- | Variational database schemas.
module VDB.Schema where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function (on)
import Data.SBV (Boolean(..))
import qualified Data.Map.Merge.Strict as StrictM
import Data.List 

import Control.Arrow (first, second)

import VDB.FeatureExpr
import VDB.Name
import VDB.Variational
import VDB.Type
import VDB.Config (Config, equivConfig)
import VDB.SAT (satisfiable)

-- | Type of a relation in the database.
-- type RowType = [Opt (Attribute, Type)]
type RowType = Map Attribute (Opt SqlType)
type TableSchema = Opt RowType

-- | Attributes must be unique in a table. The pair (Int, Attribute)
--   is for keeping the order of attributes in a relation.
-- type UniqeAttribute = (Int, Attribute)


-- | Type of a relation in the database. 
--type RelationSchema = Map UniqeAttribute (Opt Type)


-- | A schema is a mapping from relations to row types. Both the map itself and
--   each row type are optionally included. The top-level 'Opt' corresponds to
--   the feature model, which defines the set of valid configurations.
type Schema = Opt (Map Relation (TableSchema))

-- | The feature model associated with a schema.
featureModel :: Schema -> FeatureExpr
featureModel = getFexp

-- | Gets the structure of schema.
schemaStrct :: Schema -> Map Relation TableSchema
schemaStrct = getObj 

-- | Get the schema of a relation in the database.
--lookupRelationSchema :: Relation -> Schema -> Maybe (Opt RelationSchema)
--lookupRelationSchema r (_,m) = M.lookup r m

-- | returns a relation arity.
relArity :: Relation -> Schema -> Int 
relArity r s = case rt of 
                 Just rowType -> M.size rowType
                 _ -> 0
  where 
    rt = lookupRel r s

-- | get attributes of a rowtype.
getRowTypeAtts :: RowType -> Set Attribute
getRowTypeAtts = M.keysSet

-- | get attributes of a table schema.
getTableSchAtts :: TableSchema -> Set Attribute
getTableSchAtts t = getRowTypeAtts $ getObj t

-- | gets the attribute fexp conjoind with the table pres cond
--   from a table schema
-- lookupAttFexpInTableSch :: Attribute -> TableSchema -> Maybe FeatureExpr
-- lookupAttFexpInTableSch a (tf,tr) = case M.lookup a tr of 
--                                Just (f,_) 
--                                  | satisfiable f' -> Just f'
--                                  | otherwise -> Nothing
--                                    where f' = And tf f
--                                _ -> Nothing

-- -- | gets the attribute pres cond conjoined with the table pres cond
-- --   and the attribute type from a table schema.
-- lookupAttFexpTypeInTableSch :: Attribute -> TableSchema -> Maybe (Opt SqlType)
-- lookupAttFexpTypeInTableSch a (tf,tr) = case M.lookup a tr of 
--                                           Just (f,t)
--                                             | satisfiable f' -> Just (f',t)
--                                             | otherwise -> Nothing
--                                               where f' = And tf f 
--                                           _ -> Nothing

-- | get the attribute fexp from a rowtype
lookupAttFexpInRowType :: Attribute -> RowType -> Maybe FeatureExpr
lookupAttFexpInRowType a r = case M.lookup a r of 
                               Just (f,_) -> Just f
                               _ -> Nothing

-- | Get the fexp and type of an attribute in a rowtype
lookupAttFexpTypeInRowType :: Attribute -> RowType -> Maybe (Opt SqlType)
lookupAttFexpTypeInRowType = M.lookup

-- | Get attribute type pairs in a rowtype
getAttTypeFromRowType :: RowType -> Set (Attribute, SqlType)
getAttTypeFromRowType r = dropFexp rowSet
  where
    rowSet = Set.fromList $ M.assocs r
    dropFexp :: (Ord a, Ord t) => Set (a,(o,t)) -> Set (a,t)
    dropFexp = Set.map (\(a,(_,t)) -> (a,t)) 

-- | Get the schema of a relation in the database, where 
-- 	the relation schema is stored as a row type.
lookupRowType :: Relation -> Schema -> Maybe (TableSchema)
lookupRowType r (_,m) = M.lookup r m

-- | gets valid relations of a schema. i.e. relations that
--   their fexp isn't false.
getRels :: Schema -> Set Relation
getRels s = Set.filter (flip validRel $ s) rels
  where 
    rels = M.keysSet $ schemaStrct s
    validRel :: Relation -> Schema -> Bool
    validRel r s 
      | lookupRelationFexp r s == Just (Lit False) = False
      | lookupRelationFexp r s == Nothing = False
      | otherwise = True


-- | Get the feature expression of a relation in a database.
lookupRelationFexp :: Relation -> Schema -> Maybe FeatureExpr
lookupRelationFexp r s = case lookupRowType r s of 
                           Just (f,_) -> Just f
                           _ -> Nothing


-- | Get the row type of a relation in a database.
lookupRel :: Relation -> Schema -> Maybe RowType
lookupRel r s = case lookupRowType r s of 
                  Just (_,rel) -> Just rel
                  _ -> Nothing

-- | get the attributes of a relation in a database.
lookupRelAttsList :: Relation -> Schema -> Maybe [Attribute]
lookupRelAttsList r s = M.keys <$> lookupRel r s

-- | Get the type and feature exp of an attribute in a database.
lookupAttribute :: Attribute -> Relation -> Schema -> Maybe (Opt SqlType)
lookupAttribute a r s = case lookupRowType r s of 
                          Just (_,rt) -> lookupAttFexpTypeInRowType a rt
                          _ -> Nothing

-- | helper func for lookupAttInRel -- apply new rowtypes
retrieve ::  Map Attribute (Opt SqlType) -> Attribute -> Maybe (FeatureExpr, SqlType)
retrieve m a = case M.toList m of 
                [] -> Nothing
                ((x,(y,z)):xs) -> if a == x then (Just (y,z)) else retrieve (M.fromList xs) a


-- | helper func for lookupAttInRel -- old
-- retrieve :: Eq b => [(a,(b,c))] -> b -> Maybe (a,c)
-- retrieve [] _ = Nothing
-- retrieve ((x,(y,z)):xs) v = if v == y then (Just (x,z)) else retrieve xs v

-- | Get the type of an attribute in a database.
lookupAttType :: Attribute -> Relation -> Schema -> Maybe SqlType
lookupAttType a r s = case lookupAttribute a r s of 
                        Just (_,t) -> Just t
                        _ -> Nothing

-- | Get the feature expression of an attribute in adatabase.
lookupAttFexp :: Attribute -> Relation -> Schema -> Maybe FeatureExpr
lookupAttFexp a r s = case lookupAttribute a r s of 
                        Just (f,_) -> Just f
                        _ -> Nothing

-- | apply config to fexp of schema.
appConfSchemaFexp :: Config Bool -> Schema -> Bool
-- appConfSchemaFexp c s = evalFeatureExpr c (featureModel s)
-- appConfSchemaFexp c s = evalFeatureExpr c $ featureModel s
appConfSchemaFexp c = evalFeatureExpr c . featureModel

-- | applies a config to a schema. Note that it keeps the 
--   attributes and relations that aren't valid in a variant
--   associated to the config.
appConfSchema :: Config Bool -> Schema -> Schema
appConfSchema c s 
  | schemaPres = (Lit (schemaPres), 
  M.map (appConfRowType c) (appConfSchemaStrct c $ schemaStrct s))
  | otherwise = error "the schema doesn't exist for the given config!"
  where 
    schemaPres = appConfSchemaFexp c s

-- | applies a config to a schema. Note that it filters out 
--   invalid objects. Note that the schema doesn't have pres cond
--   as one of the attributes of relations.
-- Note: the following must hold for all schemas:
-- appConfSchema' c5 employeeVSchema == appConfSchema' c5 empSchema5
appConfSchema' :: Config Bool -> Schema -> Schema
appConfSchema' c s = mkOpt (Lit $ appConfSchemaFexp c s) $
  (M.filter (\optRow -> getFexp optRow == Lit True) $ schemaStrct $ appConfSchema c s)

-- | applies a given config to the structure of the schema and 
--   drops the tables that aren't valid.
appConfSchemaStrct :: Config Bool -> Map Relation TableSchema -> Map Relation TableSchema
appConfSchemaStrct c s = M.filter (\r -> if getFexp r == Lit True then True else False) s'
  where s' = M.map (appConfRowType' c) s


-- | apply config to a rowtype. it doesn't filter out invalid attributes.
appConfRowType :: Config Bool -> TableSchema -> TableSchema
appConfRowType c (f,r) = mkOpt (Lit (evalFeatureExpr c f)) $
  M.map (first $ Lit . evalFeatureExpr c) r
--  M.map (\(f,t) -> (Lit (evalFeatureExpr c f),t)) r 

-- | apply config to a rowtype. it filters out invalid attributes.
appConfRowType' :: Config Bool -> TableSchema -> TableSchema
appConfRowType' c r = updateOptObj (M.filter 
  (\optType -> getFexp optType == Lit True) $ getObj r') r'
    where r' = appConfRowType c r
  -- (Lit (evalFeatureExpr c f),
  -- M.map (first $ Lit . evalFeatureExpr c) r)
--  M.map (\(f,t) -> (Lit (evalFeatureExpr c f),t)) r 

-- | checks the equiv of two configs over a vschema.
--   TODO: need to add type constraint Boolean b!!
equivConfigOnSchema :: Schema -> Config Bool -> Config Bool -> Bool
equivConfigOnSchema s c c' = equivConfig fs c c'
  where fs = features $ featureModel s

-- | applying a feature expression to table schema and 
--   and dropping the attributes that shouldn't be present anymore.
--   i.e. their pres cond is unsatisfiable.
appFexpTableSch :: FeatureExpr -> TableSchema -> TableSchema
appFexpTableSch f t
    | satisfiable f' = mkOpt f' $ appFexpRowType f t
    | otherwise = error $ "applying the fexp " ++ show f ++ "to table schema results in an invalid table schema!!"
  where 
    f' = shrinkFeatureExpr (And f $ getFexp t)

-- | applies a feature expression to a table schema and returns a row type.
--   note that it doesn't apply the fexp to the attributes.
--   it just filters the attributes without updating their pres cond.
--   since the fexp is being conjoined with the table pres cond and
--   that would propagate to attributes too so we don't actually 
--   need to update attribute's pres cond.
appFexpRowType :: FeatureExpr -> TableSchema -> RowType
appFexpRowType f t = M.filter (\(f',_) -> satisfiable (And (And f f') $ getFexp t)) $ getObj t


-- | propagates the table pres cond to its attributes.
propagateFexpToTsch :: TableSchema -> TableSchema 
propagateFexpToTsch t = mkOpt (shrinkFeatureExpr tf) $ shrinkFexRowType $ appFexpRowType tf t
  where
    tf = getFexp t

-- | shrinks the feature expression of all attributes in a row type
shrinkFexRowType :: RowType -> RowType
shrinkFexRowType = M.map (\(f,t) -> (shrinkFeatureExpr f,t))

------------- constructing table schema (opt rowtype) ----------

-- | constructs a table schema from a list of them
combineTableSchema :: [TableSchema] -> TableSchema
combineTableSchema tss = mkOpt fexp rowType
  where
    fexp = disjFexp $ map getFexp tss
    rowType = foldl' rowTypeUnion M.empty $ map getObj tss

rowTypeUnion :: RowType -> RowType -> RowType
rowTypeUnion e e' = StrictM.merge 
                   StrictM.preserveMissing 
                   StrictM.preserveMissing 
                   matched e e'
  where 
    matched = StrictM.zipWithMaybeMatched (\_ (o,t) (o',t') -> 
      case t==t' of
        True -> Just ((Or o o'),t)
        _    -> Nothing)

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
