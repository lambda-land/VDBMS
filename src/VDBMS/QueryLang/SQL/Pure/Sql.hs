-- | Relational algebra.
module VDBMS.QueryLang.SQL.Pure.Sql where

import VDBMS.VDB.Name 
import VDBMS.QueryLang.RelAlg.Relational.Condition (RCond)

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

data SqlAttrExprBasic = 
    SqlAttr Attribute -- ^ A
  | SqlQualifiedAttr QualifiedAttr -- ^ R.A
  | SqlNullAtt -- ^ Null
  -- | SqlLitNullRenamed Attribute -- ^ Null as A
  | SqlConcatAtt Attribute [String] -- ^ concat (A, "blah", "blah")

data SqlAttrExpr =
    SqlAllAtt -- ^ *
  | SqlAttrExpr SqlAttrExprBasic
  | SqlAttrExprRenamed SqlAttrExprBasic Attribute -- ^ ... as A

data SqlRelation = 
    Rename SqlSelect
  | SqlInnerJoin SqlSelect SqlSelect (RCond SqlSelect)

data SqlBinOp = Union | UnionAll | Diff


data SqlTempRes = 
    SqlWith [Rename SqlSelect] SqlSelect
  | SqlView (Rename SqlSelect)

