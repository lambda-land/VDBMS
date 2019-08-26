-- | generates a sql query for values of SQL data type.
--   the sql query is of type Doc.
module VDBMS.QueryGen.MySql.PrintSql (

       ppSql
       , ppTempCTE
       , ppTempView

) where 

import VDBMS.QueryLang.SQL.Pure.Sql

import Text.PrettyPrint

-- | prints sql select queries.
ppSql :: SqlSelect -> Doc
ppSql (SqlSelect as ts c) = undefined
ppSql (SqlBin o l r) = undefined
ppSql (SqlTRef r) = undefined
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

-- | prints sql temporary result as CTEs.
ppTempCTE :: SqlTempRes -> Doc
ppTempCTE (SqlTemp rqs q) = undefined

-- | prints sql temporary result as views.
ppTempView :: SqlTempRes -> Doc
ppTempView (SqlTemp rqs q) = undefined




