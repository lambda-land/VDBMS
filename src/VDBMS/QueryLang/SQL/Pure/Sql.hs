-- | Relational algebra.
module VDBMS.QueryLang.SQL.Pure.Sql where
-- (

--        SqlSelect(..)
--        , SqlNullAtt(..)
--        , SqlAttrExpr(..)
--        , SqlRelation(..)
--        , SelectFromWhere(..)
--        , SqlBinOp(..)
--        , SqlTempRes(..)
--        , CteClosure
--        , AddClosure
--        , getClosure
--        , getThing
--        , aExprAtt
--        , isrel
--        , issqlslct
--        , issqlop
--        , ppSql
--        , ppTemp
--        , ppSqlString
--        , module VDBMS.QueryLang.SQL.Condition
--        , isSqlEmpty
--        , sqlconditions
--        , sqlattributes
--        , sqltables

-- ) where

import VDBMS.VDB.Name 
import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Prelude hiding ((<>), concat)
import Text.PrettyPrint
import Data.Maybe (isNothing, isJust, fromJust)


-- | final sql data type that will be sent to the database engine.
data OutSql = OutSql SelectFromWhere
  | OutSqlBin SqlBinOp OutSql OutSql
  | OutSqlEmpty

-- | the intermediate sql data type that is used to translate queries
--   written in variational relational algebra to final sql queries. 
data Sql = Sql SelectFromWhere
  | SqlBin SqlBinOp Sql Sql
  | SqlTRef Relation
  | SqlEmpty
    -- deriving Show

-- -- | Sql select statements.
-- data SqlSelect =  
--   SqlSelect SelectFromWhere
--     -- SqlSelect {
--     --   attributes :: [SqlAttrExpr],
--     --   tables :: [Rename SqlRelation],
--     --   condition :: [SqlCond SqlSelect]
--     --   -- sqlName :: Maybe Name
--     -- }
--   | SqlBin SqlBinOp SqlSelect SqlSelect -- ^ binary operator including union, difference, union all
--   | SqlTRef Relation -- ^ return a table
--   | SqlEmpty -- ^ empty query
--   -- deriving Show

-- | select-from-where
data SelectFromWhere = 
  SelectFromWhere {
      attributes :: [SqlAttrExpr]
    , tables :: [Rename SqlRelation]
    , conditions :: [SqlCond Sql] -- TODO: debateable
  }
    -- deriving Show

-- | Sql null attribute.
data SqlNullAtt = SqlNullAtt
  deriving (Eq)
  -- deriving (Eq, Show)

-- | Sql attribute projection expressions.
data SqlAttrExpr = 
    -- SqlAllAtt -- ^ *
    SqlAttr (Rename Attr) -- ^ A, A as A, R.A, R.A as A
  | SqlNullAttr (Rename SqlNullAtt) -- ^ Null, Null as A
  | SqlConcatAtt (Rename Attr) [String] -- ^ concat (A, "blah", "blah"), concat ... as A
  deriving (Eq)
  -- deriving (Eq, Show)

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
    -- SqlTRef Relation
    SqlSubQuery Sql
  | SqlInnerJoin (Rename SqlRelation) (Rename SqlRelation) RCondition
  -- | SqlMoreInnerJoin     SqlRelation       (Rename Relation) RCondition
  -- deriving Show

-- | returns true if a subquery is just a relation.
isrel :: Sql -> Bool
isrel (SqlTRef _) = True 
isrel _           = False

sqlrel :: Sql -> Relation
sqlrel (SqlTRef r) = r 
sqlrel _ = error "sql. expected sqltref"

-- | returns true if sqlselect is select ...
issqlslct :: Sql -> Bool
issqlslct (Sql _) = True
issqlslct _       = False

-- | gets attributes from sqlselect: select from where
sqlattributes :: Sql -> [SqlAttrExpr]
sqlattributes (Sql q)        = attributes q
sqlattributes (SqlBin _ l _) = sqlattributes l
sqlattributes _              = error "sql: expected select from where!"

-- | gets tables from sqlselect: select from where
sqltables :: Sql -> [Rename SqlRelation]
sqltables (Sql q) = tables q
sqltables _       = error "sql: expected select from where!"

-- | gets conditions from sqlselect: select from where
sqlconditions :: Sql -> [SqlCond Sql]
sqlconditions (Sql q) = conditions q
sqlconditions _             = error "sql: expected select from where!"

-- | returns tru if sqlselect is set op.
issqlop :: Sql -> Bool
issqlop (SqlBin _ _ _) = True
issqlop _              = False

-- | returns true if sqlselect is empty.
isSqlEmpty :: Sql -> Bool
isSqlEmpty SqlEmpty = True
isSqlEmpty _        = False

-- | Sql set operations.
data SqlBinOp = SqlUnion | SqlUnionAll | SqlDiff
  -- deriving Show

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
                         , query   :: Sql
                         }
  -- | SqlView (String, SqlSelect)

-- | CTE closure.
type CteClosure = Map Sql Name

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

-- |returns the string of output sql.
ppOutSqlString :: OutSql -> String
ppOutSqlString = render . ppOutSql

-- | prints output sql queries.
ppOutSql :: OutSql -> Doc
ppOutSql (OutSql sql) = ppSelectFromWhere sql
ppOutSql (OutSqlBin o l r) = ppSqlBin ppOutSql o l r
ppOutSql OutSqlEmpty = ppEmpty


-- | returns the string of sql select.
ppSqlString :: Sql -> String 
ppSqlString = render . ppSql

-- | prints sql select queries.
ppSql :: Sql -> Doc
ppSql (Sql sql) = ppSelectFromWhere sql
ppSql (SqlBin o l r) = ppSqlBin ppSql o l r
ppSql (SqlTRef r) = text (relationName r)
ppSql SqlEmpty = ppEmpty

-- | prints sql bin queries.
ppSqlBin :: (a -> Doc) -> SqlBinOp -> a -> a -> Doc
ppSqlBin f o l r 
  = parens (f l)
    <+> text (prettyOp o)
    <+> parens (f r)
    where
      prettyOp SqlUnion    = "UNION"
      prettyOp SqlUnionAll = "UNION ALL"
      prettyOp SqlDiff     = "EXCEPT"

ppEmpty :: Doc
ppEmpty = text "SELECT NULL"

-- | prints select from where queries.
ppSelectFromWhere :: SelectFromWhere -> Doc
ppSelectFromWhere (SelectFromWhere as ts cs)
  | not (null ts) = case (null as, null cs) of 
    (False, False) -> 
      text "SELECT"
      <+> vcomma ppAtts as
      $$ text "FROM"
      <+> vcomma ppRenameRel ts
      $$ text "WHERE"
      <+> vand ppCond cs  
    (False, True)  -> 
      text "SELECT"
      <+> vcomma ppAtts as
      $$ text "FROM"
      <+> vcomma ppRenameRel ts
    (True, False)  -> 
      text "SELECT * FROM "
      <+> vcomma ppRenameRel ts
      $$ text "WHERE"
      <+> vand ppCond cs  
    (True, True)  -> 
      text "SELECT * FROM "
      <+> vcomma ppRenameRel ts
  | otherwise = error "Sql. select from where cannot have no tables."


-- | prints sql attribute expressions.
-- TODO: this may have bugs!!!! NEED TO BE TESTED!
ppAtts :: SqlAttrExpr -> Doc
-- ppAtts SqlAllAtt = text "*"
ppAtts (SqlAttr ra) 
  | isNothing n && isNothing q = a
  | isNothing n && isJust q    
    = text ((qualName . fromJust) q) <> char '.' <> a
  | isJust n    && isNothing q = a <+> text "AS" <+> text (fromJust n)
  | isJust n    && isJust q    
    = text ((qualName . fromJust) q) 
      <> char '.' 
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
      ts = hcomma quotes (fmap text ss)

-- | prints sql relations.
ppRel :: SqlRelation -> Doc
-- ppRel (SqlTRef r) 
--   = text (relationName r)
ppRel (SqlSubQuery (SqlTRef r)) 
  = text (relationName r)
ppRel (SqlSubQuery (Sql sql)) 
  = parens (ppSelectFromWhere sql)
  -- | null (attributes sql) = ppSql sql
  -- | otherwise = parens (ppSql sql)
ppRel (SqlSubQuery q) = parens (ppSql q)
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
  -- | isrel tq = q <+> text "AS" <+> text (fromJust n)
  | otherwise =  q <+> text "AS" <+> text (fromJust n)
    where
      n = name rq
      q = (ppRel . thing) rq
      tq = thing rq

-- | prints sql conditions.
ppCond :: SqlCond Sql -> Doc
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

vand :: (a -> Doc) -> [a] -> Doc
vand = undefined

instance Show OutSql where
  show = ppOutSqlString

instance Show Sql where 
  show = ppSqlString


