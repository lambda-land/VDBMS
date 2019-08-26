-- | generates a sql query for values of SQL data type.
--   the sql query is of type Doc.
module VDBMS.QueryGen.MySql.PrintSql (

       ppSql
       , ppTempCTE
       , ppTempView

) where 

import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name

import Text.PrettyPrint

-- | prints sql select queries.
ppSql :: SqlSelect -> Doc
ppSql (SqlSelect as ts cs) 
  = text "SELECT"
    <+> vcomma ppAtts as
    $$ text "FROM"
    <+> vcomma ppRel ts
    $$ text "WHERE"
    <+> vcomma ppCond cs
ppSql (SqlBin o l r) 
  = ppSql l
    <+> text (prettyOp o)
    <+> ppSql r
    where
      prettyOp SqlUnion    = "UNION"
      prettyOp SqlUnionAll = "UNION ALL"
      prettyOp SqlDiff     = "EXCEPT"
ppSql (SqlTRef r) 
  = text "SELECT *"
    $$ text "FROM"
    <+> text (relationName r)
ppSql SqlEmpty = text "SELECT NULL"

-- | prints sql attribute expressions.
ppAtts :: SqlAttrExpr -> Doc
ppAtts SqlAllAtt = undefined
ppAtts (SqlAttr ras) = undefined
ppAtts (SqlNullAttr ra) = undefined
ppAtts (SqlConcatAtt ra s) = undefined

-- | prints sql relations.
ppRel :: SqlRelation -> Doc
ppRel (SqlSubQuery rq) = undefined
ppRel (SqlInnerJoin l r c) = undefined

-- | prints sql conditions.
ppCond :: SqlCond SqlSelect -> Doc
ppCond (SqlCond c) = undefined
ppCond (SqlIn a q) = undefined
ppCond (SqlNot c) = undefined
ppCond (SqlOr l r) = undefined
ppCond (SqlAnd l r) = undefined

-- | prints relaitonal conditions.
ppRCond :: RCondition -> Doc
ppRCond (RLit b) = undefined
ppRCond (RComp o l r) = undefined
ppRCond (RNot c) = undefined
ppRCond (ROr l r) = undefined
ppRCond (RAnd l r) = undefined

-- | prints sql temporary result as CTEs.
ppTempCTE :: SqlTempRes -> Doc
ppTempCTE (SqlTemp rqs q) = undefined

-- | prints sql temporary result as views.
ppTempView :: SqlTempRes -> Doc
ppTempView (SqlTemp rqs q) = undefined

-- | horizontal comma concat.
hcomma :: (a -> Doc) -> [a] -> Doc
hcomma f = hcat . punctuate comma . map f

-- | vertical comma concat.
vcomma :: (a -> Doc) -> [a] -> Doc
vcomma f = vcat . punctuate comma . map f


