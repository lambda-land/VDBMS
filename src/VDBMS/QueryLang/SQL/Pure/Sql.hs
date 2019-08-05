-- | Relational algebra.
module VDBMS.QueryLang.SQL.Pure.Sql where

import VDBMS.VDB.Name 
import VDBMS.QueryLang.SQL.Condition (SqlCond,RCondition)

-- | Sql select statements.
data SqlSelect =  
    SqlSelect {
      attributes :: [SqlAttrExpr],
      tables :: [SqlRelation],
      condition :: [SqlCond SqlSelect],
      sqlName :: Maybe String 
    }
  | SqlBin SqlBinOp SqlSelect SqlSelect -- ^ binary operator including union, difference, union all
  | SqlTRef Relation -- ^ return a table
  | SqlEmpty -- ^ empty query
  -- deriving Show

-- | Sql null attribute.
data SqlNullAtt = SqlNullAtt
  deriving (Eq)

-- | Sql attribute projection expressions.
data SqlAttrExpr = 
    SqlAllAtt -- ^ *
  | SqlAttr (Rename Attr) -- ^ A, A as A, R.A, R.A as A
  | SqlNullAttr (Rename SqlNullAtt) -- ^ Null, Null as A
  | SqlConcatAtt (Rename Attribute) [String] -- ^ concat (A, "blah", "blah"), concat ... as A
  deriving (Eq)

-- | Sql From expressions.
--   Note that right now since we're only using inner joins that's 
--   the only join provided.
--   Also note that if you want to cross product you'll have:
--   [Rename SqlTRef R, Rename SqlTRef T]
data SqlRelation = 
    SqlRelation (Rename SqlSelect)
  -- | SqlTwoTableInnerJoin (Rename Relation) (Rename Relation) RCondition
  -- | SqlMoreInnerJoin     SqlRelation       (Rename Relation) RCondition

-- | Sql set operations.
data SqlBinOp = SqlUnion | SqlUnionAll | SqlDiff

-- | Sql temparory storing intermediate results.
--   Note: you can only use WITH statements in a single sql query.
--         But you can use views in multiple sql queries.
--   Importnat point: do refactoring only once and then you'll have
--                    two different SQL generator!
-- so while refactoring you'll have a value of type sqltempres
-- which then can generate a cte or view!
-- Question to search: does postgres automatically run subq as cte in parallel?
-- if so it'd make our job much easier for the big union all query.
data SqlTempRes = 
    SqlTemp [Rename SqlSelect] SqlSelect
  -- | SqlView (Rename SqlSelect)

-- | Opitmized SQL queries. 
-- data SqlOptimized = 
--     SqlTemp SqlTempRes
--   | SqlNoTemp SqlSelect

