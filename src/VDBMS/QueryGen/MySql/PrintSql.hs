-- | generates a sql query for values of SQL data type.
--   the sql query is of type Doc.
module VDBMS.QueryGen.MySql.PrintSql (

       ppSql
       , ppTempCTE
       , ppTempView

) where 

import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name

import Prelude hiding ((<>))
import Text.PrettyPrint
import Data.Maybe (isNothing, isJust, fromJust)

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
ppAtts SqlAllAtt = text "*"
ppAtts (SqlAttr ra) 
  | isNothing n && isNothing q = a
  | isNothing n && isJust q    
    = text ((qualName . fromJust) q) <+> char '.' <> a
  | isJust n    && isNothing q = a <+> text "AS" <+> text (fromJust n)
  | isJust n    && isJust q    
    = text ((qualName . fromJust) q) 
      <+> char '.' 
      <> a 
      <+> text "AS" 
      <+> text (fromJust n)
    where 
      n = name ra
      q = (qualifier . thing) ra
      a = (text . attributeName . attribute . thing) ra
ppAtts (SqlNullAttr rnull) 
  | isNothing n = text "NULL"
  | isJust n    = text "NULL AS" <+> text (fromJust n)
    where
      n = name rnull
ppAtts (SqlConcatAtt ra ss) 
  | isNothing n && isNothing q = concat a
  | isNothing n && isJust q    
    = concat (text ((qualName . fromJust) q) <+> char '.' <> a)
  | isJust n    && isNothing q 
    = concat a <+> text "AS" <+> text (fromJust n)
  | isJust n    && isJust q    
    = concat (text ((qualName . fromJust) q) <+> char '.' <> a)
      <+> text "AS" <+> text (fromJust n)
    where 
      n = name ra
      q = (qualifier . thing) ra
      a = (text . attributeName . attribute . thing) ra
      concat rest = text "CONCAT" <+> parens (rest <+> comma <+> ts)
      ts = hcomma doubleQuotes (fmap text ss)

-- | prints sql relations.
ppRel :: SqlRelation -> Doc
ppRel (SqlSubQuery rq) 
  | isNothing n = q 
  | otherwise   = parens q <+> text "AS" <+> text (fromJust n)
    where
      n = name rq
      q = (ppSql . thing) rq
ppRel (SqlInnerJoin l r c) 
  = ppRel l <+> text "INNER JOIN" <+> ppRel r <+> text "ON" <+> ppRCond c

-- | prints sql conditions.
ppCond :: SqlCond SqlSelect -> Doc
ppCond (SqlCond c)  = ppRCond c
ppCond (SqlIn a q) 
  | isNothing aq = at <+> qt
  | otherwise 
    = text ((qualName . fromJust) aq) <+> char '.' <> at <+> qt
    where
      aq = qualifier a 
      at = (text . attributeName . attribute) a 
      qt = text "IN" <+> ppSql q 
ppCond (SqlNot c)   = text "NOT" <+> parens (ppCond c)
ppCond (SqlOr l r)  = ppCond l <+> text "OR" <+> ppCond r
ppCond (SqlAnd l r) = ppCond l <+> text "OR" <+> ppCond r

-- | prints relaitonal conditions.
ppRCond :: RCondition -> Doc
ppRCond (RLit b) 
  | b         = text "TRUE"
  | otherwise = text "FALSE"
ppRCond (RComp o l r) = undefined
ppRCond (RNot c)   = text "NOT" <+> parens (ppRCond c)
ppRCond (ROr l r)  = ppRCond l <+> text "OR" <+> ppRCond r
ppRCond (RAnd l r) = ppRCond l <+> text "AND" <+> ppRCond r

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


