-- | VTable data type and core operations.
module VDBMS.VDB.Table.Core (

        Table,
        getTableSchema,
        getSqlTable,
        updateSqlTable,
        mkVTable

) where 

import VDBMS.VDB.Schema.Schema
import VDBMS.DBMS.SqlTable 

-- | the result of a vq is a variational table.
--   variational table data type.
data Table = Table TableSchema SqlTable
  deriving (Eq, Show)

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
