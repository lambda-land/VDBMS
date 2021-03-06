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
import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..),Atom(..))
import VDBMS.Features.FeatureExpr.FeatureExpr

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Prelude hiding ((<>), concat)
import Text.PrettyPrint
import Data.Maybe (isNothing, isJust, fromJust)
import Data.List (delete)

-- | final sql data type that will be sent to the database engine.
-- data OutSql = OutSql SelectFromWhere
--   | OutSqlBin SqlBinOp OutSql OutSql
--   | OutSqlEmpty

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
  | SqlAndPCs [Attr] PCatt 
  | SqlAndPCFexp Attr FeatureExpr PCatt
  | SqlAndPCsFexp [Attr] FeatureExpr PCatt
  -- | SqlConcatAtt (Rename Attr) [String] -- ^ concat (A, "blah", "blah"), concat ... as A
  deriving (Eq)
  -- deriving (Eq, Show)

-- | appends the two lists of attributes for a sqlandpc.
andSqlAtts :: SqlAttrExpr -> SqlAttrExpr -> SqlAttrExpr
andSqlAtts l r 
  | isAndPCs l && isAndPCs r = SqlAndPCs (pcatts l ++ pcatts r) (pcatt l)
  | otherwise = error "andSqlAtts. sql. shouldnt be here!!"

-- | returns the list of conjuncted pc atts.
pcatts :: SqlAttrExpr -> [Attr]
pcatts (SqlAndPCs as _) = as 
pcatts _ = error "andSqlAtts. sql. shouldnt be here!!"

-- | returns the andpc attribute if it exists.
getAndPC :: [SqlAttrExpr] -> Maybe SqlAttrExpr
getAndPC as = case null as' of 
                True  -> Nothing
                False -> Just (head as')
  where as' = filter isAndPCs as

-- | adds the second list which only contains sqlattandpcs with the first
--   list. so it checks in the first list to find the andpc attribute.
--   if it finds it then it combines the list of all pcs. otherwise
--   it creates a new pc attribute.
addAttPCs2attExp :: PCatt -> [SqlAttrExpr] -> [SqlAttrExpr] -> [SqlAttrExpr]
addAttPCs2attExp pc as pcs 
  | isNothing apc = as ++ [foldr andSqlAtts (SqlAndPCs [] pc) pcs]
  | otherwise = (delete (fromJust apc) as) 
      ++  [foldr andSqlAtts (fromJust apc) pcs]
    where
      apc = getAndPC as

-- | returns the name of the pc from sqlandpcs.
pcatt :: SqlAttrExpr -> PCatt
pcatt (SqlAndPCs _ pc) = pc 
pcatt _ = error "andSqlAtts. sql. shouldnt be here!!"

-- | returns true if the attribute expression is and of pcs.
isAndPCs :: SqlAttrExpr -> Bool
isAndPCs (SqlAndPCs _ _) = True
isAndPCs _               = False

-- | is attribute expression and of pcs and is the list empty.
isAndPCsEmpty :: SqlAttrExpr -> Bool
isAndPCsEmpty (SqlAndPCs as _) = null as 
isAndPCsEmpty _                = False

-- | attributes in an attribute expr.
aExprAtt :: SqlAttrExpr -> Attribute 
-- aExprAtt SqlAllAtt 
--   = error "you have a list of attributes and not one!!!"
aExprAtt (SqlAttr ra)                         = (attribute . thing) ra
aExprAtt (SqlNullAttr (Rename Nothing _)) 
  = error "null attribute!!"
aExprAtt (SqlNullAttr (Rename (Just n) _))    = Attribute n 
aExprAtt _ = "aExprAtt. Sql. check if you should have got here!!"
-- aExprAtt (SqlConcatAtt (Rename Nothing a) _)  = attribute a 
-- aExprAtt (SqlConcatAtt (Rename (Just n) _) _) = Attribute n

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

-- | returns a relation if sqlrel is just a rel.
relFromSqlRel :: SqlRelation -> Maybe Relation
relFromSqlRel (SqlSubQuery (SqlTRef r)) = Just r
relFromSqlRel _ = Nothing

-- | returns true if a subquery is just a relation.
isrel :: Sql -> Bool
isrel (SqlTRef _) = True 
isrel _           = False

-- | returns the relation of a sqltref.
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
-- ppOutSqlString :: OutSql -> String
-- ppOutSqlString = render . ppOutSql

-- | prints output sql queries.
-- ppOutSql :: OutSql -> Doc
-- ppOutSql (OutSql sql) = ppSelectFromWhere sql
-- ppOutSql (OutSqlBin o l r) = ppSqlBin ppOutSql o l r
-- ppOutSql OutSqlEmpty = ppEmpty


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

-- | print empty. 
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
    (True, False)  -> error "sql. ppSelectFromWhere. shouldnt be here."
      -- text "SELECT * FROM "
      -- <+> vcomma ppRenameRel ts
      -- $$ text "WHERE"
      -- <+> vand ppCond cs  
    (True, True)  -> 
      -- text "SELECT * FROM "
      -- <+> 
      vcomma ppRenameRel ts
  | otherwise = error "Sql. select from where cannot have no tables."

-- | prints attr. 
ppAttr :: Attr -> Doc
ppAttr (Attr a Nothing) 
  = text (attributeName a)
ppAttr (Attr a (Just (RelQualifier r))) 
  = text (relationName r)
  <> char '.'
  <> text (attributeName a)
ppAttr (Attr a (Just (SubqueryQualifier n))) 
  = text n 
  <> char '.'
  <> text (attributeName a)

-- | print rename attr. 
ppRenameAttr :: Rename Attr -> Doc
ppRenameAttr (Rename Nothing a) = ppAttr a 
ppRenameAttr (Rename (Just n) a) = ppAttr a <+> "AS" <+> text n

-- | prints sql attribute expressions.
-- TODO: this may have bugs!!!! NEED TO BE TESTED!
ppAtts :: SqlAttrExpr -> Doc
-- ppAtts SqlAllAtt = text "*"
ppAtts (SqlAttr ra) = ppRenameAttr ra 
  -- | isNothing n && isNothing q = a
  -- | isNothing n && isJust q    
  --   = text ((qualName . fromJust) q) <> char '.' <> a
  -- | isJust n    && isNothing q = a <+> text "AS" <+> text (fromJust n)
  -- | isJust n    && isJust q    
  --   = text ((qualName . fromJust) q) 
  --     <> char '.' 
  --     <> a 
  --     <+> text "AS" 
  --     <+> text (fromJust n)
  -- | otherwise = error "the attr expr must have already matched one of the cases!"
  --   where 
  --     n = name ra
  --     q = (qualifier . thing) ra
  --     a = (text . attributeName . attribute . thing) ra
ppAtts (SqlNullAttr rnull) 
  | isNothing n = text "NULL"
  | isJust n    = text "NULL AS" <+> text (fromJust n)
  | otherwise = error "the attr expr must have already matched one of the cases!"
      where
      n = name rnull
ppAtts (SqlAndPCs as pc) = 
  text "CONCAT("
  <+> vandfexp ppAttr as
  <> ") AS "
  <> text (attributeName pc)
ppAtts (SqlAndPCFexp a f pc) = 
  text "CONCAT("
  <> quotes lparen <> comma
  <+> ppAttr a
  <> comma <+> quotes (text ") AND (") <> comma
  <+> quotes (text (show f)) <> comma <+> quotes rparen
  <> ") AS "
  <> text (attributeName pc)
ppAtts (SqlAndPCsFexp as f pc) = 
  text "CONCAT("
  <+> vandfexp ppAttr as
  -- <> quotes lparen <> comma
  -- <+> ppAttr a
  <> comma <+> quotes (text ") AND (") <> comma
  <+> quotes (text (show f)) <> comma <+> quotes rparen
  <> ") AS "
  <> text (attributeName pc)

-- ppAtts (SqlConcatAtt ra ss) 
--   | isNothing n && isNothing q = concat a
--   | isNothing n && isJust q    
--     = concat (text ((qualName . fromJust) q) <+> char '.' <> a)
--   | isJust n    && isNothing q 
--     = concat a <+> text "AS" <+> text (fromJust n)
--   | isJust n    && isJust q    
--     = concat (text ((qualName . fromJust) q) <+> char '.' <> a)
--       <+> text "AS" <+> text (fromJust n)
--   | otherwise = error "the attr expr must have already matched one of the cases!"
--     where 
--       n = name ra
--       q = (qualifier . thing) ra
--       a = (text . attributeName . attribute . thing) ra
--       concat rest = text "CONCAT" <+> parens (rest <+> comma <+> ts)
--       ts = hcomma quotes (fmap text ss)

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
    sht a@(Att _) = text (show a)
    sht v@(Val _) = quotes (text (show v))
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

-- | ands where conditions.
vand :: (a -> Doc) -> [a] -> Doc
vand f = hcat . punctuate (text " AND ") . map f 

-- | and fexps.
vandfexp :: (a -> Doc) -> [a] -> Doc
vandfexp f = hcat . punctuate (comma <+> quotes (text " AND ") <> comma) 
  . map (\a -> quotes lparen <> comma <+> f a <> comma <+> quotes rparen)

-- instance Show OutSql where
--   show = ppOutSqlString

instance Show SqlAttrExpr where
  show = render . ppAtts

instance Show Sql where 
  show = ppSqlString


