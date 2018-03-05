module VDB.ParsingSQL where 

import Prelude hiding (EQ,NEQ,LT,LTE,GTE,GT,compare)
import Control.Monad (void)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char.Lexer as L


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



-- | query ::= SELECT attrList FROM relationList WHERE condition


-- | feature ::= (any feature name)
-- | featureExpr∷= bool
--               | feature 
--               | !featureExpr
--               | featureExpr ∧featureExpr 
--               | featureExpr ∨featureExpr 


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

-- | Parser for compare operators
compareOp :: Parser CompOp 
compareOp = (symbol "=" *> pure EQ)
  <|> (symbol "!=" *> pure NEQ)
  <|> (symbol "<" *> pure LT)
  <|> (symbol "<=" *> pure LTE) 
  <|> (symbol ">=" *> pure GTE)
  <|> (symbol ">" *> pure GT)

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

-- | parse single algebra
algebra :: Parser Algebra 
algebra = selectSentence 
  <|> fromSentence 
  <|> whereSentence 
  <|> choiceSentence 

-- | Parser for SELECT 
selectSentence :: Parser Algebra 
selectSentence = do 
  reservedword "SELECT"
  alist <- attrlist
  algebra1 <- algebra 
  return (Proj alist algebra1)

-- | Parser for FROM 
fromSentence :: Parser Algebra
fromSentence = do 
  reservedword "FROM"
  tlist <- tablelist 
  return (From tlist)

-- fromSentence = undefined

-- | Parser for WHERE
whereSentence :: Parser Algebra
whereSentence = do 
  reservedword "WHERE"
  cond <- condition 
  algebra1 <- algebra
  return (Sel cond algebra1)

-- | Parser for CHOICE()
choiceSentence :: Parser Algebra
choiceSentence = do
  reservedword "CHOICE"
  void (symbol "(")
  featureExpr1 <- featureExpr 
  void (symbol ",")
  algebra1 <- algebra
  void (symbol ",")
  algebra2 <- algebra
  void (symbol ")")
  return (AChc featureExpr1 algebra1 algebra2)


-- 
-- expressions  
-- 

-- | Parse the sequence of attrubite seperated by comman
attrlist :: Parser [Attribute] 
attrlist = sepBy1 (Attribute <$> identifier) comma

-- | Parse the sequence of Relation seperated by comman
tablelist :: Parser [Relation]
tablelist = sepBy1 (Relation <$> identifier) comma

-- | Parse the condition
condition :: Parser Condition
condition = makeExprParser conTerm conOperators

-- | Define the lists with operator precedence  precedence, 
--   associativity and what constructors to use in each case.
conOperators :: [[Operator Parser Condition]]
conOperators = 
  [[Prefix (Not <$ reservedword "NOT")],
   [InfixL (And <$ reservedword "AND")],
   [InfixL (Or <$ reservedword "OR")  ]]

-- | Parse Lit Bool for Condition 
conTerm :: Parser Condition 
conTerm = (Lit True <$ reservedword "true")
  <|> (Lit False <$ reservedword "false")

-- | define a parser for comparation between atom
--   ( Comp CompOp Atom Atom)
comp :: Parser Condition 
comp = do 
  cop1 <- compareOp 
  atom1 <- atom
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

-- | define a parser for Attribute
attribute :: Parser Attribute 
attribute = Attribute <$> identifier


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
featureExpr = undefined




