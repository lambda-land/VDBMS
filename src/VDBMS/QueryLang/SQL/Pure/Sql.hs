-- | Relational algebra.
module VDBMS.QueryLang.SQL.Pure.Sql where


-- data SqlSelect = SqlSelect 
--     SqlSelect {
--       attributes :: [SqlAttrExpr],
--       tables :: [Rename SqlSelect],
--       condition :: [SqlExpr] 
--     }
--   | SqlBin SqlOp SqlQuery SqlQuery -- ^ binary operator including union, product, difference, union all
--   | SqlTRef Relation -- ^ return a table
--   | SqlEmpty -- ^ empty query
--   deriving Show

-- data SqlAttrExpr = undefined
--     SqlAttr Attribute 
--   | SqlQualifiedAtt QualifiedAttribute

-- data SqlExpr = undefined

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
