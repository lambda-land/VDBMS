-- | apply feature expression operations to sql vtable.
module VDBMS.DBMS.Table.SqlVtableApplyFexpOps (

        satFexpVtable,
        satFexpVtables,
        constSchemaFromSqlVtable,
        conformSqlVtableToSchema

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import VDBMS.Variational.Opt 
import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Table.SqlVtable
import VDBMS.DBMS.Table.Table

-- import Database.HDBC 

---------------------- applies the feature exp of vsqltable to it----------

-- | runs the sat solver on tuples to filter out tuples
--   that are unsatisfiable in the context of the vtabel
--   i.e. the feature expr assigned to it.
satFexpVtable :: PCatt -> SqlVtable -> SqlVtable
satFexpVtable p t = updateOptObj table t 
  where
    f     = getFexp t 
    table = dropRows p $ map (satFexpRow f p) $ getObj t 

-- | checks the satisfiability of a row with a fexp.
satFexpRow :: FeatureExpr -> PCatt -> SqlRow -> SqlRow
satFexpRow f p r 
  | check     = M.insert (presCondAttName p) (fexp2sqlval $ And f fp) r 
  | otherwise = M.empty
  where 
    fp    = case M.lookup (presCondAttName p) r of 
              Just fexp -> sqlval2fexp fexp 
              _         -> Lit False
    check = tautImplyFexps f fp

-- | filters out unsat tuples for a list of sqlvtables.
satFexpVtables :: PCatt -> [SqlVtable] -> [SqlVtable]
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


