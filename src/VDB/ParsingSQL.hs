
module VDB.ParsingSQL where 

import Prelude hiding (EQ,LT,GT,compare)
import Control.Monad (void)
import Data.Void
-- import Data.Data (Data,Typeable)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char.Lexer as L

-- import qualified Text.ParserCombinators.Parsec.Combinator as C


-- import VDB.Algebra
-- import Data.Data (Data,Typeable)

import VDB.Name
-- import VDB.Variational 
import VDB.Value


--  
-- Concrete syntax for VDB.SQL
-- 


-- | attribute ::= (any attribute name)

-- | attrList ::= attribute 
--              | CHOICE (featureExpr,attrList,attrList)
--              | CHOICE (featureExpr,attrList)
--              | attrList, attrList


-- | relaiton ::= (any relation name)

-- | relationList ::= relation 
--                  | CHOICE (featureExpr,relationList ,relationList)
--                  | CHOICE (featureExpr,realtionList)
--                  | relationList, relationList


-- | int ::= (Any integer)
-- | bool ::= (Any Boolean value)
-- | string ::= (any string value)

-- | atom ::= int | bool | string | attr  
-- | opt ::= <| <= | = | > | >= | !=   
-- | condition ∷= atom opt atom 
--              | NOT condition
--              | condition OR condition
--              | condition AND condition
--              | CHOICE (featureExpr,conditon ,condition)	

-- | feature ::= (any feature name)
-- | featureExpr∷= bool
--               | feature 
--               | !featureExpr
--               | featureExpr  AND featureExpr 
--               | featureExpr OR featureExpr 


-- | query :: = SELECT attrlist fromExpr whereExpr
--            | CHOICE(featureExor, query, query )

-- | fromExpr :: = FROM relationlist 
-- | whereExpr :: = WHERE condition

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


-- | vRelation ::= [relation: attrList]
-- | vRelationList ::= vRelation
--                   | vRelaiton, vRelaitonList
-- | vSchema ::= featureExpr ? {vRelationList}

-- ** TO DO: RelConc --> fixed

--
-- * Abstract Syntax for SQL
--

-- | An attrList is a list of Attribute. Empty list is not allowed.
data AttrList 
   = A Attribute  
   | Attr2Chc FeatureExpr AttrList AttrList
   | Attr1Chc FeatureExpr AttrList
   | AConcat AttrList AttrList
  deriving (Eq,Show)

-- | A RelationList is a list of relation / Choice of relation. Empty list is not allowed. 
data RelationList 
   = R Relation
   | Rel2Chc FeatureExpr RelationList RelationList
   | Rel1Chc FeatureExpr RelationList 
   | RelConcat RelationList RelationList
  deriving (Eq,Show)

-- | Query expression. SELECT ... FROM ... WHERE ...
data Query = Select AttrList FromExpr WhereExpr
           | QChc FeatureExpr Query Query
  deriving (Eq,Show)

-- | FROM ... 
data FromExpr  = From RelationList
  deriving (Eq,Show)

-- | Where ...
data WhereExpr = Where Condition
  deriving (Eq,Show)

-- | Boolean expressions over features.
data FeatureExpr
   = FLit Bool
   | FRef Feature
   | FNot FeatureExpr
   | FAnd FeatureExpr FeatureExpr
   | FOr  FeatureExpr FeatureExpr
  deriving (Eq,Show)

-- | Atoms are the leaves of a condition.
data Atom
   = Val  Value
   | Attr Attribute
  deriving (Eq,Show)

-- | Variational conditions.
data Condition
   = CLit  Bool
   | CComp CompOp Atom Atom
   | CNot  Condition
   | COr   Condition Condition
   | CAnd  Condition Condition
   | CChc FeatureExpr Condition Condition
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
-- Parser for Query
--

-- | parse v-query
query :: Parser Query 
query = selectExpr 
  <|> choiceExpr 

-- | Parser for SELECT 
selectExpr :: Parser Query 
selectExpr = do 
  reservedword "SELECT"
  alist <- attrlistExpr
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
  rlist <- relationlistExpr
  return (From rlist)

whereExpr :: Parser WhereExpr
whereExpr = do 
  reservedword "WHERE"
  cond <- condition
  return (Where cond)

-- 
-- Parser for AttrList  
-- 

-- | Parser for AttrList
attrlistExpr :: Parser AttrList
attrlistExpr = makeExprParser attrlistTerm attrlistOperators

-- | define a parser for Attribute
attribute :: Parser Attribute 
attribute = Attribute <$> identifier

-- | attrlistTerm is defining the terms for AttrList 
attrlistTerm :: Parser AttrList
attrlistTerm =  attr1Choice
  <|> attr2Choice
  <|> A <$> attribute
  <|> parens attrlistExpr
  
-- | define the operator(,) for AttrList, in the case of concatenate the list
attrlistOperators :: [[Operator Parser AttrList]]
attrlistOperators =
  [ [ InfixL (AConcat <$ symbol ",")]]


-- | Used to parse attrlist in CHOICE() function,
--   the list of attribute should be closed by parenthesis 
attrlistExprAsParameter :: Parser AttrList
attrlistExprAsParameter = parens attrlistExpr 
 <|> A <$> attribute
 <|> attr2Choice

-- | Parser for the choice in AttrList (AttrChc)
attr2Choice :: Parser AttrList
attr2Choice = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr
  void (symbol ",")
  a1 <- attrlistExprAsParameter
  void (symbol ",")
  a2 <- attrlistExprAsParameter
  void (symbol ")")
  return (Attr2Chc featureExpr1 a1 a2)

attr1Choice :: Parser AttrList
attr1Choice = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr
  void (symbol ",")
  a1 <- attrlistExprAsParameter
  void (symbol ")")
  return (Attr1Chc featureExpr1 a1)

--
-- Parser for RelationList
--
relationlistExpr :: Parser RelationList
relationlistExpr = makeExprParser relationlistTerm relationlistOperators

-- | define a parser for a single Relation 
relation :: Parser Relation
relation = Relation <$> identifier

-- | define the Terms in RelationList 
relationlistTerm :: Parser RelationList
relationlistTerm =  relation2Choice
  <|> R <$> relation
  <|> parens relationlistExpr
  
-- | define the Operators in relationList
--   in case of relationList seperated by ,
relationlistOperators :: [[Operator Parser RelationList]]
relationlistOperators =
  [ [ InfixL (RelConcat <$ symbol ",")]]

-- | Used to parse the RelationList in CHOICE() function,
--   NOTE: a list of relation as parameter should be 
--   enclosed by parenthesis
relationlistExprAsParameter :: Parser RelationList
relationlistExprAsParameter = parens relationlistExpr 
 <|> R <$> relation
 <|> relation2Choice

-- | Parser for 2 choices in RelationList (Rel2Chc)
relation2Choice :: Parser RelationList
relation2Choice = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr
  void (symbol ",")
  a1 <- relationlistExprAsParameter
  void (symbol ",")
  a2 <- relationlistExprAsParameter
  void (symbol ")")
  return (Rel2Chc featureExpr1 a1 a2)

-- | Parser for 1 choice in RelationList (Rel1Chc)
relation1Choice :: Parser RelationList
relation1Choice = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr
  void (symbol ",")
  a1 <- relationlistExprAsParameter
  void (symbol ")")
  return (Rel1Chc featureExpr1 a1)

--
-- Parser for FeatureExpr
--

-- | define a parser for featureExpr
featureExpr :: Parser FeatureExpr 
featureExpr = makeExprParser featureTerm featureOperators
  <|> parens featureExpr  

-- | define the terms in featureExpr
featureTerm :: Parser FeatureExpr
featureTerm = FRef <$> feature 
  <|> (FLit True <$ reservedword "true")
  <|> (FLit False <$ reservedword "false")

-- | define the operators in featureExpr
featureOperators :: [[Operator Parser FeatureExpr]]
featureOperators =
  [[Prefix (FNot <$ reservedword "NOT")],
   [InfixL (FAnd <$ reservedword "AND"),
    InfixL (FOr <$ reservedword "OR")  ]]

-- | Parser for single Feature
feature :: Parser Feature
feature = Feature <$> identifier


-- 
-- Parser for Condition
-- 

-- | Parse the condition
condition :: Parser Condition
condition = makeExprParser conTerm conOperators


-- | Define the lists with operator precedence, 
--   associativity and what constructors to use in each case.
conOperators :: [[Operator Parser Condition]]
conOperators = 
  [[Prefix (CNot <$ reservedword "NOT")],
   [InfixL (CAnd <$ reservedword "AND"),
    InfixL (COr <$ reservedword "OR")  ]]

-- | Parse Lit Bool for Condition 
conTerm :: Parser Condition 
conTerm =  parens comp
  <|> (CLit True <$ reservedword "true")
  <|> (CLit False <$ reservedword "false")
  <|> comp
  <|> conditionChoice


-- | define a parser for comparation between atom
--   ( Comp CompOp Atom Atom)
comp :: Parser Condition 
comp = do 
  atom1 <- atom
  cop1 <- compareOp 
  atom2 <- atom
  return (CComp cop1 atom1 atom2)

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

-- | 
conditionAsParameter :: Parser Condition
conditionAsParameter = condition 
 <|> parens condition
 <|> conditionChoice

-- | Parse for CChc FeatureExpr Condition Condition 
conditionChoice :: Parser Condition 
conditionChoice = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr
  void (symbol ",")
  c1 <- conditionAsParameter
  void (symbol ",")
  c2 <- conditionAsParameter
  void (symbol ")")
  return (CChc featureExpr1 c1 c2)

