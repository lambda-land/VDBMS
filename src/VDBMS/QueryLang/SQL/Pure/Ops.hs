-- | simple operations on sql queries.
module VDBMS.QueryLang.SQL.Pure.Ops (

       adjustQSch
       , updatePC
       , sqlQAtts

) where

import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr

-- import VDBMS.VDB.Schema.Relational.Types (RSchema)
-- import VDBMS.VDB.Schema.Relational.Lookups (rlookupAttsList)

-- import Control.Monad.Catch 
import Data.Maybe (fromJust)

-- | gets attributes projected in a sqlselect query.
--   queries are type correct.
sqlQAtts :: SqlSelect -> [Attribute]
sqlQAtts (SqlSelect as _ _) = map aExprAtt as
sqlQAtts (SqlBin _ l _) = sqlQAtts l
sqlQAtts SqlEmpty = []

-- | adjusts the schema  of a sql query wrt a given list of attribute.
adjustQSch :: [Attribute] -> [Attribute] -> SqlSelect -> SqlSelect
adjustQSch resAtts qsAtts (SqlSelect as ts cs)
  = SqlSelect (updatesAs resAtts qsAtts as) ts cs
adjustQSch resAtts qsAtts (SqlBin o l r) 
  = SqlBin o (adjustQSch resAtts qsAtts l) (adjustQSch resAtts qsAtts r)
adjustQSch resAtts qsAtts q@(SqlTRef _)  -- should never even get here!
  = undefined
--   = error "SHOULD NEVER GET SQLTREF RELATION!! IN ADJUSTING THE SCHEMA OF QUERIES!!"
--   = SqlSelect (updatesAs resAtts qsAtts [SqlAllAtt]) [SqlSubQuery (Rename Nothing q)] []
adjustQSch resAtts qsAtts SqlEmpty = undefined
  -- = SqlSelect (updatesAs resAtts qsAtts []) [SqlSubQuery (Rename Nothing SqlEmpty)] []

-- | adjusts a list of sql attr expr. 
--   i.e. adds atts in res as null to aes.
updatesAs :: [Attribute] -> [Attribute] -> [SqlAttrExpr] -> [SqlAttrExpr]
updatesAs res _ [] 
  = fmap (\a -> SqlNullAttr (Rename ((Just . attributeName) a) SqlNullAtt)) res
-- updatesAs res already [SqlAllAtt] 
--   = fmap update res
--   where 
--     update a
--       | a `elem` already = SqlAttr (Rename Nothing (Attr a Nothing))
--       | otherwise 
--         = SqlNullAttr (Rename ((Just . attributeName) a) SqlNullAtt)
updatesAs res already aes 
  = fmap update res
  where
    ates = fmap (\e -> (aExprAtt e, e)) aes 
    update a 
      | a `elem` already = fromJust $ lookup a ates
      | otherwise
        = SqlNullAttr (Rename ((Just . attributeName) a) SqlNullAtt)

-- | updates the queries in order to add the given feature expr 
--   to tuples presence condition. the queries passed to this 
--   function are either of the format of sqlselect as ts cs
--   or sqlbin o l r. this function is used for combining 
--   sql queries with the same schema into one query in genOneQ.
updatePC :: PCatt -> SqlSelect -> FeatureExpr -> SqlSelect
updatePC p (SqlSelect as ts cs) f
  = SqlSelect 
    (as ++ [SqlConcatAtt (Rename Nothing (Attr p Nothing)) 
                         [" AND " ++ show f]]) 
    ts 
    cs 
updatePC p (SqlBin o l r) f
  = SqlBin o (updatePC p l f) (updatePC p r f)
updatePC _ _ _ = error 
  "expected a sqlselect value!! but got either tref or empty!!!"






