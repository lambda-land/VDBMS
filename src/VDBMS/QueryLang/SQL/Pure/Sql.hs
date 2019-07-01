-- | Relational algebra.
module VDBMS.QueryLang.SQL.Pure.Sql where

import VDBMS.VDB.Name 
import VDBMS.QueryLang.RelAlg.Relational.Condition (RCond)

-- | Sql select statements.
data SqlSelect =  
    SqlSelect {
      attributes :: [SqlAttrExpr],
      tables :: [SqlRelation],
      condition :: [RCond SqlSelect] 
    }
  | SqlBin SqlBinOp SqlSelect SqlSelect -- ^ binary operator including union, difference, union all
  | SqlTRef Relation -- ^ return a table
  | SqlEmpty -- ^ empty query
  -- deriving Show

-- | Basic Sql attribute projection expressions.
data SqlAttrExprBasic = 
    SqlAttr Attribute -- ^ A
  | SqlQualifiedAttr QualifiedAttr -- ^ R.A
  | SqlNullAtt -- ^ Null
  -- | SqlLitNullRenamed Attribute -- ^ Null as A
  | SqlConcatAtt Attribute [String] -- ^ concat (A, "blah", "blah")

-- | Sql attribute project expression with renaming.
data SqlAttrExpr =
    SqlAllAtt -- ^ *
  | SqlAttrExpr SqlAttrExprBasic
  | SqlAttrExprRenamed SqlAttrExprBasic Attribute -- ^ ... as A

-- | Sql From expressions.
--   Note that right now since we're only using inner joins that's 
--   the only join provided.
--   Also note that if you want to cross product you'll have:
--   [Rename SqlTRef R, Rename SqlTRef T]
data SqlRelation = 
    SqlRelation (Rename SqlSelect)
  | SqlTwoTableInnerJoin (Rename Relation) (Rename Relation) (RCond SqlSelect)
  | SqlMoreInnerJoin     SqlRelation         (Rename Relation)   (RCond SqlSelect)

-- | Sql set operations.
data SqlBinOp = Union | UnionAll | Diff

-- | Sql temparory storing intermediate results.
--   Note: you can only use WITH statements in a single sql query.
--         But you can use views in multiple sql queries.
data SqlTempRes = 
    SqlWith [Rename SqlSelect] SqlSelect
  | SqlView (Rename SqlSelect)

