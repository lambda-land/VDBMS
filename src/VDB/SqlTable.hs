-- | Tables returned by HDBC.
module VDB.SqlTable where

-- import Data.Map
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (deleteBy,groupBy)

import VDB.Variant 
import VDB.Variational 
import VDB.Name
import VDB.Config
import VDB.FeatureExpr 
import VDB.Schema
import VDB.Type
import VDB.SAT 

import Database.HDBC 

-- type Row = [SqlValue]
-- type Table = [Row]
-- type Vtable = Opt Table

-- type ClmNameIncludedRow = [(String, SqlValue)]
-- type ClmNameIncludedTable = [ClmNameIncludedRow]
-- type ClmNameIncludedVariantTable = Variant ClmNameIncludedTable Bool
-- type ClmNameIncludedVtable = Opt ClmNameIncludedTable

-- type ClmRowMap = Map String SqlValue
-- type ClmTableMap = [ClmRowMap]
-- type ClmVariantTableMap = Variant ClmTableMap Bool
-- type ClmVtableMap = Opt ClmTableMap

type SqlRow = Map String SqlValue
type SqlTable = [SqlRow]
type SqlVariantTable = Variant SqlTable Bool
type SqlVtable = Opt SqlTable

type VTuple = Opt SqlRow
type VTuples = [VTuple]

-- | returns a set of attributes from a tuple.
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
rowAttSet :: SqlRow -> Set Attribute
rowAttSet = S.map (Attribute Nothing) . M.keysSet 

-- | returns a set of attributes from a table.
tableAttSet :: SqlTable -> Set Attribute
tableAttSet [] = error "an empty table doesn't have any attributes"
tableAttSet t  = rowAttSet (head t)

-- | construct the rowtype from a sqltable.
--   NOTE: it takes the first row of the table. so if that row
--         has a null value it may not be able to get the type 
--         correctly. for now make sure you never have a null
--         value in the first tuple. but fix it later!!
-- TODO: FIX THE ABOVE PROBLEM!!
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
constRowTypeOfSqlTable :: FeatureExpr -> SqlTable -> RowType
constRowTypeOfSqlTable f t = M.map (\v -> (f,v)) row''
  where 
    row   = head t 
    row'  = M.mapKeys (\s -> Attribute Nothing s) row 
    row'' = M.map typeOf row'

-- | inserts an attribute value pair to a sqlrow.
insertAttValToSqlRow :: Attribute -> SqlValue -> SqlRow -> SqlRow
insertAttValToSqlRow = M.insert . attributeName

-- | inserts an attribute value pair into all rows of a sqltable.
insertAttValToSqlTable :: Attribute -> SqlValue -> SqlTable -> SqlTable
insertAttValToSqlTable a v = map $ insertAttValToSqlRow a v 

-- | forces a sqlrow to conform to a rowtype
conformSqlRowToRowType :: SqlRow -> RowType -> SqlRow
conformSqlRowToRowType r t = M.union r r'
  where
    rowTypeAtts = S.map attributeName $ getRowTypeAtts t 
    attDif      = rowTypeAtts S.\\ M.keysSet r 
    r'          = M.fromSet (\_ -> SqlNull) attDif

-- | removes tuples that have the same values except for pres
--   cond, inserts only one such tuple and disjuncts all 
--   their pres conds.
-- NOTE: time this separately!!
disjoinDuplicate :: PresCondAtt -> SqlTable -> SqlTable
disjoinDuplicate p t = destVTuples p shrinkedFexpRes
-- destVTuples p resTs -- just disjoins duplicate tuples
-- destVTuples p dropFalseRowsRes -- also drops tuples with false fexp
-- destVTuples p shrinkedFexpRes-- also shrinks fexp of tuples
  where
    vtuples :: VTuples
    vtuples = constVTuples p t 
    groupedTs :: [VTuples]
    groupedTs = groupBy (\x y -> snd x == snd y) vtuples
    groupedFexpTs :: [([FeatureExpr],SqlRow)]
    groupedFexpTs = map pushDownList groupedTs
    mapFst g (a,b) = (g a,b)
    resTs = map (mapFst disjFexp) groupedFexpTs
    dropFalseRowsRes = filter (satisfiable . fst) resTs
    shrinkedFexpRes = map (mapFst shrinkFeatureExpr) dropFalseRowsRes


-- | constructs a list of fexp for the group of vtuples
--   that have the same tuple.
--   NOTE: this is unsafe since you're not checking if 
--         the first element of pairs are the same!
pushDownList :: [(a,b)] -> ([a],b)
pushDownList [(a,b)] = ([a],b)
pushDownList ((a,b):l) = (a:fst (pushDownList l),b)

-- | extract the pres cond out of sqlrow and attachs it
--   as the presence condition to the tuple.
constVTuple :: PresCondAtt -> SqlRow -> VTuple
constVTuple p r = mkOpt f t 
  where 
    pName = presCondAttName p
    f = case M.lookup pName r of
          Just v -> sqlval2fexp v
          _      -> Lit False
    t = M.delete pName r

-- | constructs a table of vtuples.
constVTuples :: PresCondAtt -> SqlTable -> VTuples
constVTuples p t = map (constVTuple p) t

-- | destructs a vtuple into a sqlrow.
destVTuple :: PresCondAtt -> VTuple -> SqlRow
destVTuple p t = M.insert (presCondAttName p) (fexp2sqlval $ getFexp t) $ getObj t

-- | destructs a vtuples into a sqltable.
destVTuples :: PresCondAtt -> VTuples -> SqlTable
destVTuples p ts = map (destVTuple p) ts 

------------------- apply config ----------------------

-- | applies a config to a row.
applyConfRow :: Config Bool -> PresCondAtt -> SqlRow -> SqlRow 
applyConfRow c p r = M.adjust updatePres (presCondAttName p) r 
  where 
    -- pres = M.lookup p r 
    updatePres :: SqlValue -> SqlValue
    updatePres v = fexp2sqlval $ Lit $ evalFeatureExpr c (sqlval2fexp v)
    -- pres' = evalFeatureExpr c (sqlToFexp pres)

-- | applies a config to a table.
applyConfTable :: Config Bool -> PresCondAtt -> SqlTable -> SqlTable
applyConfTable c p = fmap $ applyConfRow c p

-- | drops a row if it's pres cond is false.
dropRow :: PresCondAtt -> SqlRow -> SqlRow
dropRow p r 
  | M.lookup (presCondAttName p) r == Just (toSql ("Lit False" :: String))
              = M.empty
  | otherwise = r

-- | drops rows that their pres cond is false.
dropRows :: PresCondAtt -> SqlTable -> SqlTable
dropRows p t = deleteBy (==) M.empty $ fmap (dropRow p) t
-- dropRows c p = fmap $ M.filterWithKey filterRow
--   where filterRow att val = att == presCondAttName p 
--                             -- && val == SqlString "Lit False"
--                             && val == toSql ("Lit False" :: String)

-- filterWithKey :: (k -> a -> Bool) -> Map k a -> Map k a

-- | drops the pres cond key value in a row.
dropPres :: PresCondAtt -> SqlRow -> SqlRow
dropPres p = M.delete (presCondAttName p)

-- | drops the pres cond key value in a table.
dropPresInTable :: PresCondAtt -> SqlTable -> SqlTable
dropPresInTable p = fmap $ dropPres p

-- | applies a config to tables.
applyConfTables :: Config Bool -> PresCondAtt -> [SqlTable] -> [SqlTable]
applyConfTables c p = fmap $ applyConfTable c p

-- | applies the variant config to the variant table.
applyConfVariantTable :: PresCondAtt -> SqlVariantTable -> SqlVariantTable
applyConfVariantTable p t = updateVariant (applyConfTable c p $ getVariant t) t
  where c = getConfig t

-- | drops rows with false pres cond in a variant table.
dropRowsInVariantTable :: PresCondAtt -> SqlVariantTable -> SqlVariantTable
dropRowsInVariantTable p t = updateVariant (dropRows p $ getVariant (applyConfVariantTable p t)) t
  where c = getConfig t

-- | applies the variant config to variant tables.
applyConfVariantTables :: PresCondAtt -> [SqlVariantTable] -> [SqlVariantTable]
applyConfVariantTables p = fmap $ applyConfVariantTable p

-- | drops rows with false pres cond over a list of variant tables.
dropRowsInVariantTables :: PresCondAtt -> [SqlVariantTable] -> [SqlVariantTable]
dropRowsInVariantTables p = fmap $ dropRowsInVariantTable p 

-- | drops the pres key value of all rows in a variant table.
dropPresInVariantTable :: PresCondAtt -> SqlVariantTable -> SqlVariantTable
dropPresInVariantTable p t = updateVariant (dropPresInTable p (getVariant t)) t

-- | generates the relation schema (rowtype) of a variant table.
constructSchemaFromSqlVariantTable :: SqlVariantTable -> TableSchema
constructSchemaFromSqlVariantTable t = (fexp, rowType)
  where
    fexp    = conf2fexp $ getConfig t 
    table   = getVariant t
    rowType = constRowTypeOfSqlTable fexp table
-- constructSchemaFromSqlVariantTable :: SqlVariantTable -> TableSchema
-- constructSchemaFromSqlVariantTable t = (fexp, rowType)
--   where
--     fexp = conf2fexp $ getConfig t 
--     row = head $ getVariant t
--     row' = M.mapKeys (\s -> Attribute s) row 
--     row'' = M.map typeOf row'
--     rowType = M.map (\v -> (fexp,v)) row''

-- | forces a sqlvarianttable to conform to a table schema. i.e. 
--   it adds all attributes in the schema to the sqlvarianttable
--   with sqlnull.
--   TODO and DISCUSS WITH ERIC: maybe we should insert some specific
--                               value (like nothing) to specify that
--                               this value doesn't actually exist!
conformSqlVariantTableToSchema :: SqlVariantTable -> RowType -> SqlVariantTable
conformSqlVariantTableToSchema t r = updateVariant 
  (map (flip conformSqlRowToRowType r) $ getVariant t) t
 --  where 
    
-- | adds presence condition key and its value to each row
--   of the sqlvarianttable and turns it into a vtable.
--   NOTE: sqlvarianttable shouldn't have pres cond in its
--         attributes.
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
addTuplePresCond :: PresCondAtt -> SqlVariantTable -> SqlTable
addTuplePresCond p vt = insertAttValToSqlTable (Attribute Nothing $ presCondAttName p) fexp t
  where 
    fexp = fexp2sqlval $ conf2fexp $ getConfig vt
    t    = getVariant vt

---------------------- applies the feature exp of vsqltable to it----------

-- | runs the sat solver on tuples to filter out tuples
--   that are unsatisfiable in the context of the vtabel
--   i.e. the feature expr assigned to it.
satFexpVtable :: PresCondAtt -> SqlVtable -> SqlVtable
satFexpVtable p t = updateOptObj table t 
  where
    f     = getFexp t 
    table = dropRows p $ map (satFexpRow f p) $ getObj t 

-- | checks the satisfiability of a row with a fexp.
satFexpRow :: FeatureExpr -> PresCondAtt -> SqlRow -> SqlRow
satFexpRow f p r 
  | check     = M.insert (presCondAttName p) (fexp2sqlval $ And f fp) r 
  | otherwise = M.empty
  where 
    fp    = case M.lookup (presCondAttName p) r of 
              Just fexp -> sqlval2fexp fexp 
              _         -> Lit False
    check = filterFexps f fp

-- | filters out unsat tuples for a list of sqlvtables.
satFexpVtables :: PresCondAtt -> [SqlVtable] -> [SqlVtable]
satFexpVtables p = map $ satFexpVtable p 

-- | constructs the table schema from the sqlvtable.
constSchemaFromSqlVtable :: SqlVtable -> TableSchema
constSchemaFromSqlVtable t = mkOpt f $ constRowTypeOfSqlTable f table
  where 
    f     = getFexp t 
    table = getObj t 

-- | forces a sqlvtable to conform to a rowtype
conformSqlVtableToSchema :: SqlVtable -> RowType -> SqlVtable
conformSqlVtableToSchema t r = updateOptObj 
  (map (flip conformSqlRowToRowType r) $ getObj t) t 


