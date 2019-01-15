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