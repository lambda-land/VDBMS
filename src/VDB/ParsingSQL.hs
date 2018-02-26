module VDB.ParsingSQL where 

import Control.Monad (void)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Char.Lexer as L

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


--
--  Lexer
--

-- | spaceConsumer: consume the whitespace, newline,
--                  line comment out, block comment out 
spaceConsumer :: Parser ()
spaceConsumer = L.space space1 newline lineCmnt blockCmnt 
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
integer :: Parser Integer
integer = lexeme L.decimal

-- | 'comma' parses a comma ","
comma :: Parser String 
comma = symbol ","

-- | parses the reservedwords and identifiers 
reservedWord :: String -> Parser ()
reservedword w = lexeme (string w *> notFollowedBy alphaNumChar)

-- | list of reserved words
reservedwords :: [String]
reservedwords = ["SELECT", "FROM", "WHERE", "OR", "AND", "NOT"]

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




