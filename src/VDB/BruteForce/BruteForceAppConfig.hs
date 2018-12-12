-- Applies the configuration to the result of queries sent to the db
-- in the brute force approach.
module VDB.BruteForce.BruteForceAppConfig where 

import qualified VDB.FeatureExpr as F
import VDB.BruteForce.BruteForceSendQs
import VDB.Config
import VDB.Name (PresCondAtt(..))
import VDB.SqlTable

import Data.Map.Strict (adjust)

-- | applies a configuration to a row and updates the presence 
--   condition of the row to either true or false depending on
--   evaluating the pres cond under config.
applyConfigRow :: ClmRowMap -> PresCondAtt -> Config Bool -> ClmRowMap
applyConfigRow r p c = 
  adjust 
    (\pres -> F.fexp2sqlval 
             (F.Lit $ F.evalFeatureExpr c (F.sqlval2fexp pres))) 
    (presCondAttName p) r 

-- | applies a config to a table.
applyConfigTable :: ClmTableMap -> PresCondAtt -> Config Bool -> ClmTableMap
applyConfigTable t p c = map ((flip4 applyConfigRow) p c) t

-- | aux func for applyConfigTable
flip4 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip4 f b c a = f a b c

-- | takes a variant table and applies its config to it.
applyConfigVariantTable :: ClmVariantTableMap -> PresCondAtt -> ClmVariantTableMap
applyConfigVariantTable (c,t) p = (c, applyConfigTable t p c)

-- | takes a list of variant tables and applies their config to them.
applyConfigVariantTables :: PresCondAtt -> [ClmVariantTableMap] -> [ClmVariantTableMap]
applyConfigVariantTables p = map ((flip applyConfigVariantTable) p)

