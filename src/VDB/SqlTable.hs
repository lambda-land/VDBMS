-- | Tables returned by HDBC.
--   TODO: do I need to check sth or add functions?
--         look into table.hs to ensure (for adding funcs)!
module VDB.SqlTable where

-- import Data.Map
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.List (deleteBy)

import VDB.Variant 
import VDB.Variational (Opt)
import VDB.Name
import VDB.Config
import VDB.FeatureExpr 
import VDB.Schema
import VDB.Type

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

-- | returns a set of attributes from a tuple.
rowAttSet :: SqlRow -> Set Attribute
rowAttSet = S.map Attribute . M.keysSet 

-- | returns a set of attributes from a table.
tableAttSet :: SqlTable -> Set Attribute
tableAttSet [] = error "an empty table doesn't have any attributes"
tableAttSet t  = rowAttSet (head t)

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
--   NOTE: it takes the first row of the table. so if that row
--         has a null value it may not be able to get the type 
--         correctly. for now make sure you never have a null
--         value in the first tuple. but fix it later!!
-- TODO: FIX THE ABOVE PROBLEM!!
constructSchemaFromSqlVariantTable :: SqlVariantTable -> TableSchema
constructSchemaFromSqlVariantTable t = (fexp, rowType)
  where
    fexp = conf2fexp $ getConfig t 
    row = head $ getVariant t
    row' = M.mapKeys (\s -> Attribute s) row 
    row'' = M.map typeOf row'
    rowType = M.map (\v -> (fexp,v)) row''

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
    
-- | forces a sqlrow to conform to a rowtype
conformSqlRowToRowType :: SqlRow -> RowType -> SqlRow
conformSqlRowToRowType r t = M.union r r'
  where
    rowTypeAtts = S.map attributeName $ getRowTypeAtts t 
    attDif = rowTypeAtts S.\\ M.keysSet r 
    r' = M.fromSet (\_ -> SqlNull) attDif

-- | adds presence condition key and its value to each row
--   of the sqlvarianttable and turns it into a vtable.
--   NOTE: sqlvarianttable shouldn't have pres cond in its
--         attributes.
addTuplePresCond :: PresCondAtt -> SqlVariantTable -> SqlTable
addTuplePresCond p vt = insertAttValToSqlTable (Attribute $ presCondAttName p) fexp t
  where 
    fexp = fexp2sqlval $ conf2fexp $ getConfig vt
    t = getVariant vt


-- | inserts an attribute value pair to a sqlrow.
insertAttValToSqlRow :: Attribute -> SqlValue -> SqlRow -> SqlRow
insertAttValToSqlRow = M.insert . attributeName

-- | inserts an attribute value pair into all rows of a sqltable.
insertAttValToSqlTable :: Attribute -> SqlValue -> SqlTable -> SqlTable
insertAttValToSqlTable a v = map $ insertAttValToSqlRow a v 


