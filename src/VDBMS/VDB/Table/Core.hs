-- | VTable data type and core operations.
module VDBMS.VDB.Table.Core (

        Table
        , getTableSchema
        , getSqlTable
        , updateSqlTable
        , mkVTable

) where 

import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Table.Table 
import VDBMS.VDB.Name (PCatt)

import Text.PrettyPrint

-- | the result of a vq is a variational table.
--   variational table data type.
data Table = Table TableSchema SqlTable
  -- deriving (Eq)

equivTabs :: Table -> Table -> Bool
equivTabs l r = (getTableSchema l == getTableSchema r)
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
