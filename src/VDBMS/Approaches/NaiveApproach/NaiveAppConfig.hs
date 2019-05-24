-- Applies the configuration to the result of queries sent to the db
-- in the brute force approach. **It's not filtering out tuples with
-- FALSE pres cond! at least not for now!!
module VDBMS.Approaches.NaiveApproach.NaiveAppConfig where 

import qualified VDBMS.Features.FeatureExpr as F
import VDBMS.Approaches.NaiveApproach.NaiveSendQs
import VDBMS.Features.Config
import VDBMS.VDB.Name (PresCondAtt(..))
import VDBMS.DBMS.SqlTable

import Data.Map.Strict (adjust)

-- | applies a configuration to a row and updates the presence 
--   condition of the row to either true or false depending on
--   evaluating the pres cond under config.
applyConfigRow :: SqlRow -> PresCondAtt -> Config Bool -> SqlRow
applyConfigRow r p c = 
  adjust 
    (\pres -> F.fexp2sqlval 
             (F.Lit $ F.evalFeatureExpr c (F.sqlval2fexp pres))) 
    (presCondAttName p) r  

-- | applies a config to a table.
applyConfigTable :: SqlTable -> PresCondAtt -> Config Bool -> SqlTable
applyConfigTable t p c = map ((flip4 applyConfigRow) p c) t

-- | aux func for applyConfigTable
flip4 :: (a -> b -> c -> d) -> b -> c -> a -> d
flip4 f b c a = f a b c

-- | takes a variant table and applies its config to it.
applyConfigVariantTable :: SqlVariantTable -> PresCondAtt -> SqlVariantTable
applyConfigVariantTable (t,c) p = (applyConfigTable t p c, c)

-- | takes a list of variant tables and applies their config to them.
applyConfigVariantTables :: PresCondAtt -> [SqlVariantTable] -> [SqlVariantTable]
applyConfigVariantTables p = map ((flip applyConfigVariantTable) p)

-- update :: Ord k => (a -> Maybe a) -> k -> Map k a -> Map k a
-- | aaplies a config to a row and filters it out if its prescond = false
-- TODO: complete this and adjust the rest accordingly. keep in mind 
-- that this could also be done when packing the result and pretty print it!
-- if you do it in the 
applyConfigFilterRow :: SqlRow -> PresCondAtt -> Config Bool -> Maybe SqlRow
applyConfigFilterRow r p c = undefined
-- update updatePres (presCondAttName p) r
