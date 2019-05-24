-- | Feature expression parser.
module VDBMS.Features.FeatureExpr.Parser (

        fexpParser

) where

import Data.ByteString.Char8 as BC (pack, unpack)
import qualified Data.ByteString as B 
import Data.Void (Void)

import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Byte.Lexer as L
import Text.Megaparsec.Byte 

import VDBMS.Features.Feature
import VDBMS.Features.FeatureExpr.Types



-- -- feature expression parser
type Parser = Parsec Void B.ByteString
-- -- type Parser' = ParsecT Void B.ByteString (Either )

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 empty empty
-- -- (L.skipLineComment "line comment") 
-- -- (L.skipBlockComment "starting block comment" "end block comment")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: B.ByteString -> Parser B.ByteString
symbol = L.symbol spaceConsumer

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

rservedWord :: B.ByteString -> Parser ()
rservedWord w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

reservedWords :: [B.ByteString]
reservedWords = ["not", "true", "false", "and", "or"]

identifier :: Parser String
identifier = BC.unpack <$> (lexeme . try) (p >>= check)
  where
    p = B.cons <$> letterChar <*> (B.pack <$> many alphaNumChar)
    -- p = (:) <$> letterChar <*> many alphaNumChar

    check x
      | x `elem` reservedWords = fail $ "keyword " ++ show x ++ " is reserved"
      | otherwise = return x

fexpParser :: Parser FeatureExpr
fexpParser = makeExprParser fExp fOperators


fOperators :: [[Operator Parser FeatureExpr]]
fOperators =
  [ [Prefix (Not <$ rservedWord "not") ]
  , [InfixL (And <$ rservedWord "and")
    , InfixL (Or <$ rservedWord "or") ]
  ]


fExp :: Parser FeatureExpr
fExp =  parens fexpParser
  <|> (Lit True  <$ rservedWord "true")
  <|> (Lit False <$ rservedWord "false")
  <|> Ref . Feature <$> identifier 

