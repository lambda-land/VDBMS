-- | Tables returned by HDBC.
--   TODO: do I need to check sth or add functions?
--         look into table.hs to ensure (for adding funcs)!
module VDB.SqlTable where

-- import Data.Map
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

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
applyConfTable c p = map $ applyConfRow c p

-- | applies a config to tables.
applyConfTables :: Config Bool -> PresCondAtt -> [SqlTable] -> [SqlTable]
applyConfTables c p = map $ applyConfTable c p

-- | applies the variant config to the variant table.
applyConfVariantTable :: PresCondAtt -> SqlVariantTable -> SqlVariantTable
applyConfVariantTable p t = mkVariant (applyConfTable c p $ getVariant t) c
  where c = getConfig t

-- | applies the variant config to variant tables.
applyConfVariantTables :: PresCondAtt -> [SqlVariantTable] -> [SqlVariantTable]
applyConfVariantTables p = map $ applyConfVariantTable p

