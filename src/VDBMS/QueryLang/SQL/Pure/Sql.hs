-- | Relational algebra.
module VDBMS.QueryLang.SQL.Pure.Sql where

import VDBMS.VDB.Name 
import VDBMS.QueryLang.RelAlg.Relational.Condition (RCondition)

data SqlSelect =  
    SqlSelect {
      attributes :: [SqlAttrExpr],
      tables :: [SqlRelation],
      condition :: [RCondition SqlSelect] 
    }
  | SqlBin SqlBinOp SqlSelect SqlSelect -- ^ binary operator including union, difference, union all
  | SqlTRef Relation -- ^ return a table
  | SqlEmpty -- ^ empty query
  -- deriving Show

data SqlAttrExprBasic = 
    SqlAttr Attribute -- ^ A
  | SqlQualifiedAtt QualifiedAttribute -- ^ R.A
  | SqlNullAtt -- ^ Null
  -- | SqlLitNullRenamed Attribute -- ^ Null as A
  | SqlConcatAtt Attribute [String] -- ^ concat (A, "blah", "blah")

data SqlAttrExpr =
    SqlAllAtt -- ^ *
  | SqlAttrExpr SqlAttrExprBasic
  | SqlAttrExprRenamed SqlAttrExprBasic Attribute -- ^ ... as A

data SqlRelation = 
    Rename SqlSelect
  | SqlInnerJoin SqlSelect SqlSelect (RCondition SqlSelect)

data SqlBinOp = Union | UnionAll | Diff


data SqlTempRes = 
    SqlWith [Rename SqlSelect] SqlSelect
  | SqlView (Rename SqlSelect)

-- 
-- haskelldb sql type:
--
-- data SqlSelect  = SqlSelect { 
--                              options   :: [String],                -- ^ DISTINCT, ALL etc.
--            attrs     :: [(SqlColumn,SqlExpr)],   -- ^ result
--                              tables    :: [(SqlTable,SqlSelect)],  -- ^ FROM
--                              criteria  :: [SqlExpr],               -- ^ WHERE
--                              groupby   :: Maybe Mark,   -- ^ GROUP BY
--                              orderby   :: [(SqlExpr,SqlOrder)],    -- ^ ORDER BY
--            extra     :: [String]                 -- ^ TOP n, etc.
--                             }
--                 | SqlBin   String SqlSelect SqlSelect -- ^ Binary relational operator
--                 | SqlTable SqlTable -- ^ Select a whole table.
--                 | SqlEmpty -- ^ Empty select.
--   deriving Show

-- data SqlExpr = ColumnSqlExpr  SqlColumn
--              | BinSqlExpr     String SqlExpr SqlExpr
--              | PrefixSqlExpr  String SqlExpr
--              | PostfixSqlExpr String SqlExpr
--              | FunSqlExpr     String [SqlExpr]
--              | AggrFunSqlExpr String [SqlExpr] -- ^ Aggregate functions separate from normal functions.
--              | ConstSqlExpr   String
--        | CaseSqlExpr    [(SqlExpr,SqlExpr)] SqlExpr
--              | ListSqlExpr    [SqlExpr]
--              | ExistsSqlExpr  SqlSelect
--              | ParamSqlExpr (Maybe SqlName) SqlExpr
--              | PlaceHolderSqlExpr
--              | ParensSqlExpr SqlExpr
--              | CastSqlExpr String SqlExpr 
--   deriving Show
