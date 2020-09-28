-- | VTable data type and core operations.
module VDBMS.VDB.Table.Core (

        Table
        , getTableSchema
        , getSqlTable
        , updateSqlTable
        , mkVTable
        , confTable

) where 

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Table.Table 
import VDBMS.VDB.Name (PCatt)
import VDBMS.Features.Config (Config)
import VDBMS.VDB.Schema.Relational.Types (rtableSchAtts)

import Text.PrettyPrint
import Data.List ((\\))
import Debug.Trace

-- | the result of a vq is a variational table.
--   variational table data type.
data Table = Table TableSchema SqlTable
  -- deriving (Eq)

-- | configures a table for a given conf.
confTable :: PCatt -> Config Bool -> Table -> SqlTable
confTable p c t = validTuples
  where
    nonvalidAtt = tableSchAtts tsch \\ rtableSchAtts confedTsch
    confedTsch = configTableSchema_ c tsch
    tsch = getTableSchema t
    satTuplesNoPc = dropPresInTable p $ dropUnsatTuples (tschFexp tsch) p (getSqlTable t)
    validTuples = dropAttsFromSqlTable nonvalidAtt satTuplesNoPc

-- | determines if two tables are equivalent.
equivTabs :: Table -> Table -> Bool
equivTabs l r = trace ("schema : " ++ show (getTableSchema l == getTableSchema r)
  ++ "\n" ++ "tables : " ++ show (equivSqlTables (getSqlTable l) (getSqlTable r)))
  (getTableSchema l == getTableSchema r)
  && equivSqlTables (getSqlTable l) (getSqlTable r)

instance Eq Table where
  (==) = equivTabs

-- | pretty prints a table.
prettyTable :: PCatt -> Table -> String
prettyTable pc t = render tabPrinted
  where
    tabPrinted = text (ppTableSchema tsch)
              $$ text (prettySqlTable (tableSchAtts tsch ++ [pc]) 
                                      (getSqlTable t))
    tsch = getTableSchema t

instance Show Table where
  show = prettyTable "prescond"


-- | returns the schema of the vtable.
getTableSchema :: Table -> TableSchema
getTableSchema (Table s _) = s 

-- | returns the table of the vtable.
getSqlTable :: Table -> SqlTable
getSqlTable (Table _ t) = t

-- | updates the sqltable of a vtable given a function.
updateSqlTable :: (SqlTable -> SqlTable) -> Table -> Table
updateSqlTable f (Table s t) = Table s $ f t

-- | generates a vtable.
mkVTable :: TableSchema -> SqlTable -> Table
mkVTable s t = Table s t
