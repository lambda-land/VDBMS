-- | Tables returned by HDBC.
module VDBMS.DBMS.Table.Table (

        SqlRow,
        SqlTable,
        rowAttSet,
        tableAttSet,
        constRowTypeOfSqlTable,
        insertAttValToSqlTable,
        conformSqlRowToRowType,
        dropPresInTable,
        applyConfTable,
        applyConfTables,
        dropRows

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

import VDBMS.VDB.Name
import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Schema.Schema
import VDBMS.DBMS.Value.Value
import VDBMS.Features.SAT 

import Database.HDBC (SqlValue(..))

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

-- | returns a set of attributes from a tuple.
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
rowAttSet :: SqlRow -> Set Attribute
rowAttSet = S.map Attribute . M.keysSet 

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
    row'  = M.mapKeys (\s -> Attribute s) row 
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

-----------apply conf------------------

-- | drops a row if it's pres cond is false.
dropRow :: PresCondAtt -> SqlRow -> SqlRow
dropRow p r 
  | M.lookup (presCondAttName p) r == Just (fexp2sqlval $ Lit False)
  -- (toSql ("Lit False" :: String))
              = M.empty
  | otherwise = r

-- | drops rows that their pres cond is false.
dropRows :: PresCondAtt -> SqlTable -> SqlTable
dropRows p t = filter (/= M.empty) $ fmap (dropRow p) t
  -- deleteBy (/=) M.empty $ fmap (dropRow p) t
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

-- | applies a config to a row.
applyConfRow :: Config Bool -> Set Attribute -> PresCondAtt -> SqlRow -> SqlRow 
applyConfRow c as p r = M.adjust updatePres (presCondAttName p) r'
  where 
    -- pres = M.lookup p r 
    updatePres :: SqlValue -> SqlValue
    updatePres v = fexp2sqlval $ Lit $ evalFeatureExpr c (sqlval2fexp v)
    r' = M.restrictKeys r $ S.insert (presCondAttName p) $ S.map attributeName as 
    -- pres' = evalFeatureExpr c (sqlToFexp pres)

-- | applies a config to a table.
applyConfTable :: Config Bool -> Set Attribute -> PresCondAtt -> SqlTable -> SqlTable
applyConfTable c as p = fmap $ applyConfRow c as p

-- | applies a config to tables.
applyConfTables :: Config Bool -> Set Attribute -> PresCondAtt -> [SqlTable] -> [SqlTable]
applyConfTables c as p = fmap $ applyConfTable c as p



