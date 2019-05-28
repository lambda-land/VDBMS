-- | apply feature expression operations to sql vtable.
module VDBMS.DBMS.SqlTable.SqlVtableApplyFexpOps (

        satFexpVtable,
        satFexpVtables,
        constSchemaFromSqlVtable,
        conformSqlVtableToSchema

) where

-- import Data.Map
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
-- import Data.Set (Set)
-- import qualified Data.Set as S
-- import Data.List (deleteBy,groupBy)

-- import VDBMS.Features.Variant 
import VDBMS.Variational.Opt 
import VDBMS.VDB.Name
-- import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.FeatureExpr
-- import VDBMS.Features.ConfFexp
import VDBMS.VDB.Schema.Schema
import VDBMS.DBMS.Value.Value
-- import VDBMS.Features.SAT 
import VDBMS.DBMS.SqlTable.SqlVtable
import VDBMS.DBMS.SqlTable.SqlTable

import Database.HDBC 

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


