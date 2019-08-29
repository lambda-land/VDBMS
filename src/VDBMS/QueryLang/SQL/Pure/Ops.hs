-- | simple operations on sql queries.
module VDBMS.QueryLang.SQL.Pure.Ops (

       adjustQSch

) where

import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name
-- import VDBMS.VDB.Schema.Relational.Types (RSchema)
-- import VDBMS.VDB.Schema.Relational.Lookups (rlookupAttsList)

-- import Control.Monad.Catch 
import Data.Maybe (fromJust)

-- | adjusts the schema  of a sql query wrt a given list of attribute.
adjustQSch :: [Attribute] -> [Attribute] -> SqlSelect -> SqlSelect
adjustQSch resAtts qsAtts (SqlSelect as ts cs)
  = SqlSelect (updatesAs resAtts qsAtts as) ts cs
adjustQSch resAtts qsAtts (SqlBin o l r) 
  = SqlBin o (adjustQSch resAtts qsAtts l) (adjustQSch resAtts qsAtts r)
adjustQSch resAtts qsAtts q@(SqlTRef r) 
  = SqlSelect (updatesAs resAtts qsAtts [SqlAllAtt]) [SqlSubQuery (Rename Nothing q)] []
adjustQSch resAtts qsAtts SqlEmpty
  = SqlSelect (updatesAs resAtts qsAtts []) [SqlSubQuery (Rename Nothing SqlEmpty)] []

-- | adjusts a list of sql attr expr. 
--   i.e. adds atts in res as null to aes.
updatesAs :: [Attribute] -> [Attribute] -> [SqlAttrExpr] -> [SqlAttrExpr]
updatesAs res _ [] 
  = fmap (\a -> SqlNullAttr (Rename ((Just . attributeName) a) SqlNullAtt)) res
updatesAs res already [SqlAllAtt] 
  = fmap update res
  where 
    update a
      | a `elem` already = SqlAttr (Rename Nothing (Attr a Nothing))
      | otherwise 
        = SqlNullAttr (Rename ((Just . attributeName) a) SqlNullAtt)
updatesAs res already aes 
  = fmap update res
  where
    ates = fmap (\e -> (aExprAtt e, e)) aes 
    update a 
      | a `elem` already = fromJust $ lookup a ates
      | otherwise
        = SqlNullAttr (Rename ((Just . attributeName) a) SqlNullAtt)