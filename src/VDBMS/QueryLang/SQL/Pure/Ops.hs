-- | simple operations on sql queries.
module VDBMS.QueryLang.SQL.Pure.Ops (

       -- qAtts
       adjustQSch

) where

import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name
-- import VDBMS.VDB.Schema.Relational.Types (RSchema)
-- import VDBMS.VDB.Schema.Relational.Lookups (rlookupAttsList)

-- import Control.Monad.Catch 
-- import Data.Maybe (fromJust)

-- | returns the list of attributes in a query.
-- qAtts :: SqlSelect -> RSchema -> [Attribute]
-- qAtts (SqlSelect as ts cs) s = undefined
-- qAtts (SqlBin o l r) s = qAtts l s 
-- qAtts (SqlTRef r) s = fromJust $ rlookupAttsList r s
-- qAtts SqlEmpty _ = []

-- -- | returns the list of attributes from an attribute expression.
-- attExpAtts :: SqlAttrExpr -> [Attribute]
-- attExpAtts SqlAllAtt = undefined
-- attExpAtts (SqlAttr ra) = undefined
-- attExpAtts (SqlNullAttr rn) = undefined
-- attExpAtts (SqlConcatAtt ra ss) = undefined

-- | adjusts the schema  of a sql query wrt a given list of attribute.
adjustQSch :: [Attribute] -> [Attribute] -> SqlSelect -> SqlSelect
adjustQSch = undefined