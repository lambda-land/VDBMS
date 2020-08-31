-- | generates a sql query for values of SQL data type.
--   the sql query is of type Doc.
module VDBMS.QueryGen.MySql.PrintSql (

       ppSql
       , ppTemp
       , ppSqlString

) where 

import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name

import Prelude hiding ((<>), concat)
import Text.PrettyPrint
import Data.Maybe (isNothing, isJust, fromJust)

-- | returns the string of sql select.
ppSqlString :: SqlSelect -> String 
ppSqlString = render . ppSql

-- | prints sql select queries.
ppSql :: SqlSelect -> Doc
ppSql (SqlSelect as ts cs) 
  | null as && null cs = 
     vcomma ppRenameRel ts
  | null cs = text "SELECT"
    <+> vcomma ppAtts as
    $$ text "FROM"
    <+> vcomma ppRenameRel ts
  | otherwise = text "SELECT"
    <+> vcomma ppAtts as
    $$ text "FROM"
    <+> vcomma ppRenameRel ts
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
ppSql SqlEmpty = text "SELECT NULL"

-- | prints sql attribute expressions.
-- TODO: this may have bugs!!!! NEED TO BE TESTED!
ppAtts :: SqlAttrExpr -> Doc
-- ppAtts SqlAllAtt = text "*"
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
  | otherwise = error "the attr expr must have already matched one of the cases!"
    where 
      n = name ra
      q = (qualifier . thing) ra
      a = (text . attributeName . attribute . thing) ra
ppAtts (SqlNullAttr rnull) 
  | isNothing n = text "NULL"
  | isJust n    = text "NULL AS" <+> text (fromJust n)
  | otherwise = error "the attr expr must have already matched one of the cases!"
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
  | otherwise = error "the attr expr must have already matched one of the cases!"
    where 
      n = name ra
      q = (qualifier . thing) ra
      a = (text . attributeName . attribute . thing) ra
      concat rest = text "CONCAT" <+> parens (rest <+> comma <+> ts)
      ts = hcomma doubleQuotes (fmap text ss)

-- | prints sql relations.
ppRel :: SqlRelation -> Doc
ppRel (SqlTRef r) 
  = text (relationName r)
ppRel (SqlSubQuery q) 
  | null (attributes q) = ppSql q
  | otherwise = parens (ppSql q)
ppRel (SqlInnerJoin l r c) 
  = ppRenameRel l 
 <+> text "INNER JOIN" 
 <+> ppRenameRel r 
 <+> text "ON" 
 <+> ppRCond c

-- | prints rename sqlrel.
ppRenameRel :: Rename SqlRelation -> Doc 
ppRenameRel rq 
  | isNothing n = q
  | isrel tq = q <+> text "AS" <+> text (fromJust n)
  | otherwise = parens q <+> text "AS" <+> text (fromJust n)
    where
      n = name rq
      q = (ppRel . thing) rq
      tq = thing rq

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
ppRCond (RComp o l r) = sht l <> (text . show) o <> sht r
  where 
    sht = text . show
ppRCond (RNot c)   = text "NOT" <+> parens (ppRCond c)
ppRCond (ROr l r)  = ppRCond l <+> text "OR" <+> ppRCond r
ppRCond (RAnd l r) = ppRCond l <+> text "AND" <+> ppRCond r

-- | prints sql temporary resul.
ppTemp :: SqlTempRes -> Doc
ppTemp (SqlCTE rqs q) = undefined
  -- = text "WITH"
  --   <+> hcomma rqt rqs
  --   <+> ppSql q
  --   where
  --     rqt (n,q') = text n <+> text "AS" <+> parens (ppSql q')
-- ppTemp (SqlView (n, q)) 
--   = text "CREATE VIEW"
--     <+> text n 
--     <+> text "AS"
--     <+> ppSql q

-- | horizontal comma concat.
hcomma :: (a -> Doc) -> [a] -> Doc
hcomma f = hcat . punctuate comma . map f

-- | vertical comma concat.
vcomma :: (a -> Doc) -> [a] -> Doc
vcomma f = vcat . punctuate comma . map f
