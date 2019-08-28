-- | simple operations on sql queries.
module VDBMS.QueryLang.SQL.Pure.Ops (

       qAtts
       , adjustQSch

) where


import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name
import VDBMS.VDB.Schema.Relational.Types (RSchema)

-- | returns the list of attributes in a query.
qAtts :: SqlSelect -> RSchema -> [Attribute]
qAtts = undefined

-- | adjusts the schema  of a sql query wrt a given list of attribute.
adjustQSch :: [Attribute] -> SqlSelect -> RSchema -> SqlSelect
adjustQSch = undefined