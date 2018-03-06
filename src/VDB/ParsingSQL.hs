module VDB.ParsingSQL where 

import Prelude hiding (EQ,NEQ,LT,LTE,GTE,GT,compare)
import Control.Monad (void)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char.Lexer as L

import qualified Text.ParserCombinators.Parsec.Combinator as C


import VDB.Algebra
import Data.Data (Data,Typeable)

import VDB.Name
import VDB.FeatureExpr (FeatureExpr)
import VDB.Condition
import VDB.Variational 
import VDB.Value


--  
-- Concrete syntax for VDB.SQL
-- 


-- | attribute ::= (any attribute name)

-- | attrList ::= attribute 
--              | CHOICE (featureExpr,attrList,attrList)
--              | attibute, attrList


-- | relaiton ::= (any relation name)

-- | relationList ::= relation 
--                  | CHOICE (featureExpr,tableList ,tableList)
--                  | relationList CROSSJOIN relationList


-- | int ::= (Any integer)
-- | bool ::= (Any Boolean value)
-- | string ::= (any string value)

-- | atom ::= int | bool | string | attr  
-- | opt ::= <| <= | = | > | >= | !=   
-- | condition ∷= atom opt atom 
--              | !condition
--              | condition OR condition
--              | condition AND condition
--              | CHOICE (featureExpr,conditon ,condition)	


-- | query :: = SELECT attrlist fromExpr whereExpr
--            | CHOICE(featureExor, query, query )
-- | fromExpr :: = FROM relationlist 
-- | whereExpr :: = WHERE condition


-- | feature ::= (any feature name)
-- | featureExpr∷= bool
--               | feature 
--               | !featureExpr
--               | featureExpr  AND featureExpr 
--               | featureExpr OR featureExpr 


-- 
-- * Traditional schema in SQL
-- * (Define a schema in traditional SQL by create one table per time)
-- 

-- | dataType ::= (any table type)

-- | attrAndType ::= attribute datatype  

-- | attrAndTypeList ::= attrAndType
--                     | attrAndType, attrAndTypeList

-- | createRelation ::= CREATE TABLE relation (attrAndTypeList);

--
-- * Variational schema
-- * (Relation associated with varialtional relation) 
-- 


-- | vRelation: ::= [relation: attrList]
-- | vRelationList ::= vRelation
--                   | vRelaiton, vRelaitonList
-- | vSchema ::= featureExpr ? {vRelationList}


--
-- * Syntax for SQL
--


-- | An attrList is a list of Attribute. Empty list is not allowed.
-- data AttrList 
--    = A Attribute  
--    | AChc FeatureExpr AttrList AttrList
--    | AConcat AttrList AttrList
--   deriving (Eq,Show)

-- | singleAttr includes plain attribute and variational attributelist
data SingleAttr 
   = A Attribute  
   | AttrChc FeatureExpr [SingleAttr] [SingleAttr]
  deriving (Eq,Show)

-- | singleRelation includes a plain attribute and variational relationList 
data SingleRelation  
   = R Relation
   | RelChc FeatureExpr [SingleRelation] [SingleRelation]
  deriving (Eq,Show)

-- | Query expression. SELECT ... FROM ... WHERE ...
-- data Query = SELECT AttrList FromExpr WhereExpr
--            | QChc FeatureExpr Query Query
--   deriving (Eq,Show)

data Query = Select [SingleAttr] FromExpr WhereExpr
           | QChc FeatureExpr Query Query
  deriving (Eq,Show)

-- | FROM ... 
data FromExpr  = From [SingleRelation]
  deriving (Eq,Show)

-- | Where ...
data WhereExpr = Where Condition 
  deriving (Eq,Show)

type Parser = Parsec Void String
--
--  Lexer
--

-- | spaceConsumer: consume the whitespace, newline,
--                  line comment out, block comment out 
spaceConsumer :: Parser ()
spaceConsumer = L.space space1 lineCmnt blockCmnt 
  where lineCmnt = L.skipLineComment "--"
        blockCmnt = L.skipBlockComment "/*" "*/"

-- | Wrap parser for 'lexeme'
lexeme :: Parser a -> Parser a 
lexeme = L.lexeme spaceConsumer

-- | A helper to parse symbols (special string)
symbol :: String -> Parser String 
symbol = L.symbol spaceConsumer

-- | 'parens' parse things between parenthesis 
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | 'integer' parses an integer
integer :: Parser Int
integer = lexeme L.decimal

-- | 'comma' parses a comma ","
comma :: Parser String 
comma = symbol ","

-- | newline parsers a newline "\n"
newline :: Parser String
newline = symbol "\n"

-- | parses the reservedwords and identifiers 
reservedword :: String -> Parser ()
reservedword w = lexeme (string w *> notFollowedBy alphaNumChar)

-- | list of reserved words
reservedwords :: [String]
reservedwords = ["SELECT", "FROM", "WHERE", "CHOICE", "OR", "AND", "NOT", "true", "false"]

-- | ? 
identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many alphaNumChar
    check x = if x `elem` reservedwords
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x



--
-- Parser
--

-- algebra :: Parser Algebra 
-- algebra = do  
--   reservedword "SELECT" 
--   alist <- attrlist
--   reservedword "FROM"
--   tlist <- tablelist 
--   reservedword "WHERE"
--   cond <- condition 
--   return ()

-- | parse v-query
query :: Parser Query 
query = selectExpr 
  <|> choiceExpr 

-- | Parser for SELECT 
selectExpr :: Parser Query 
selectExpr = do 
  reservedword "SELECT"
  alist <- attrlist
  fromExpr1 <- fromExpr
  whereExpr1 <- whereExpr
  return (Select alist fromExpr1 whereExpr1)

-- | Parser for CHOICE()
choiceExpr :: Parser Query
choiceExpr = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr 
  void (symbol ",")
  query1 <- query
  void (symbol ",")
  query2 <- query
  void (symbol ")")
  return (QChc featureExpr1 query1 query2)

fromExpr :: Parser FromExpr
fromExpr = do 
  reservedword "FROM"
  rlist <- relationlist
  return (From rlist)

whereExpr :: Parser WhereExpr
whereExpr = do 
  reservedword "WHERE"
  cond <- condition
  return (Where cond)

-- 
-- expressions  
-- 

-- | Parse the sequence of attrubite seperated by comman
attrlist :: Parser [SingleAttr] 
attrlist = sepBy1 singleAttr comma 
-- | Parse single A Attribute
singleAttr :: Parser SingleAttr
singleAttr = A <$> attribute
  <|> choiceAttr

choiceAttr :: Parser SingleAttr
choiceAttr = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr 
  void (symbol ",")
  a1 <- attrlist
  void (symbol ",")
  a2 <- attrlist
  void (symbol ")")
  return (AttrChc featureExpr1 a1 a2)

-- | Parse the sequence of relation seperated by comman
relationlist :: Parser [SingleRelation] 
relationlist = sepBy1 singleRelation comma 

-- | Parse single SingleRelation
singleRelation :: Parser SingleRelation
singleRelation = R <$> relation
  <|> choiceRelation

-- | Parse choice on relation
choiceRelation :: Parser SingleRelation
choiceRelation = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr 
  void (symbol ",")
  r1 <- relationlist
  void (symbol ",")
  r2 <- relationlist
  void (symbol ")")
  return (RelChc featureExpr1 r1 r2)

-- | define a parser for Attribute
attribute :: Parser Attribute 
attribute = Attribute <$> identifier

-- | define a parser for Relation
relation :: Parser Relation
relation = Relation <$> identifier

-- | Parse the condition
condition :: Parser Condition
condition = makeExprParser conTerm conOperators

-- | Define the lists with operator precedence  precedence, 
--   associativity and what constructors to use in each case.
conOperators :: [[Operator Parser Condition]]
conOperators = 
  [[Prefix (Not <$ reservedword "NOT")],
   [InfixL (And <$ reservedword "AND"),
    InfixL (Or <$ reservedword "OR")  ]]

-- | Parse Lit Bool for Condition 
conTerm :: Parser Condition 
conTerm =  parens comp
  <|> (Lit True <$ reservedword "true")
  <|> (Lit False <$ reservedword "false")
  <|> comp
  <|> choiceCondition

choiceCondition :: Parser Condition 
choiceCondition = undefined

-- | define a parser for comparation between atom
--   ( Comp CompOp Atom Atom)
comp :: Parser Condition 
comp = do 
  atom1 <- atom
  cop1 <- compareOp 
  atom2 <- atom
  return (Comp cop1 atom1 atom2)

-- | define a parser for Atom 
atom :: Parser Atom 
atom = Val <$> val
  <|> Attr <$> attribute 

-- | define a parser for Value
val :: Parser Value
val = I <$> integer 
  <|> (B True <$ reservedword "true")
  <|> (B False <$ reservedword "false")
  <|> S <$> identifier

-- | Parser for compare operators
compareOp :: Parser CompOp 
compareOp = (symbol "=" *> pure EQ)
  <|> (symbol "!=" *> pure NEQ)
  <|> (symbol "<" *> pure LT)
  <|> (symbol "<=" *> pure LTE) 
  <|> (symbol ">=" *> pure GTE)
  <|> (symbol ">" *> pure GT)

-- | Parse for CChc FeatureExpr Condition Condition 
-- cchc :: Parser Condition 
-- cchc = do 
--   reservedword "CHOICE"
--   void (symbol "(")
--   featureExpr1 <- featureExpr
--   void (symbol ",")
--   cond1 <- condition 
--     void (symbol ",")
--   cond2 <- condition 
--   void (symbol ")")
--   return (CChc featureExpr1 cond1 cond2)

-- | define a parser for featureExpr
featureExpr :: Parser FeatureExpr 
featureExpr = makeExprParser featureTerm featureOperators

featureTerm :: Parser FeatureExpr
featureTerm = undefined

featureOperators :: [[Operator Parser FeatureExpr]]
featureOperators = undefined




