-- | Relational algebra.
module VDBMS.QueryLang.SQL.Pure.Sql (

       SqlSelect(..)
       , SqlNullAtt(..)
       , SqlAttrExpr(..)
       , SqlRelation(..)
       , SqlBinOp(..)
       , SqlTempRes(..)
       , CteClosure
       , AddClosure
       , getClosure
       , getThing
       , aExprAtt
       , module VDBMS.QueryLang.SQL.Condition

) where

import VDBMS.VDB.Name 
import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

-- | Sql select statements.
data SqlSelect =  
    SqlSelect {
      attributes :: [SqlAttrExpr],
      tables :: [Rename SqlRelation],
      condition :: [SqlCond SqlSelect]
      -- sqlName :: Maybe String 
    }
  | SqlBin SqlBinOp SqlSelect SqlSelect -- ^ binary operator including union, difference, union all
  -- | SqlTRef Relation -- ^ return a table
  | SqlEmpty -- ^ empty query
  -- deriving Show

-- | Sql null attribute.
data SqlNullAtt = SqlNullAtt
  deriving (Eq)

-- | Sql attribute projection expressions.
data SqlAttrExpr = 
    -- SqlAllAtt -- ^ *
    SqlAttr (Rename Attr) -- ^ A, A as A, R.A, R.A as A
  | SqlNullAttr (Rename SqlNullAtt) -- ^ Null, Null as A
  | SqlConcatAtt (Rename Attr) [String] -- ^ concat (A, "blah", "blah"), concat ... as A
  deriving (Eq)

-- | attributes in an attribute expr.
aExprAtt :: SqlAttrExpr -> Attribute 
-- aExprAtt SqlAllAtt 
--   = error "you have a list of attributes and not one!!!"
aExprAtt (SqlAttr ra)                         = (attribute . thing) ra
aExprAtt (SqlNullAttr (Rename Nothing _)) 
  = error "null attribute!!"
aExprAtt (SqlNullAttr (Rename (Just n) _))    = Attribute n 
aExprAtt (SqlConcatAtt (Rename Nothing a) _)  = attribute a 
aExprAtt (SqlConcatAtt (Rename (Just n) _) _) = Attribute n

-- | Sql From expressions.
--   Note that right now since we're only using inner joins that's 
--   the only join provided.
--   Also note that if you want to cross product you'll have:
--   [Rename SqlTRef R, Rename SqlTRef T]
data SqlRelation = 
    SqlTRef Relation
  | SqlSubQuery SqlSelect
  | SqlInnerJoin (Rename SqlRelation) (Rename SqlRelation) RCondition
  -- | SqlMoreInnerJoin     SqlRelation       (Rename Relation) RCondition

-- | Sql set operations.
data SqlBinOp = SqlUnion | SqlUnionAll | SqlDiff

-- | Sql temparory storing intermediate results.
--   Note: you can only use WITH statements in a single sql query.
--         But you can use views in multiple sql queries.
-- Note: i'm not doing the important point anymore!!
--   Importnat point: do refactoring only once and then you'll have
--                    two different SQL generator!
-- so while refactoring you'll have a value of type sqltempres
-- which then can generate a cte or view!
-- Question to search: does postgres automatically run subq as cte in parallel?
-- if so it'd make our job much easier for the big union all query.
data SqlTempRes = SqlCTE { closure :: CteClosure
                         , query   :: SqlSelect
                         }
  -- | SqlView (String, SqlSelect)

-- | CTE closure.
type CteClosure = Map SqlSelect Name

-- | couples up closure with something else.
type AddClosure a = (a, CteClosure)

-- | returns the closure.
getClosure :: AddClosure a -> CteClosure
getClosure = snd 

-- | returns the thing.
getThing :: AddClosure a -> a 
getThing = fst 

-- | Opitmized SQL queries. 
-- data SqlOptimized = 
--     SqlTemp SqlTempRes
--   | SqlNoTemp SqlSelect

