-- | Feature expressions.
module VDB.FeatureExpr where

import Data.Data (Data,Typeable)

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.ByteString.Char8 as BC (pack, unpack)
import qualified Data.ByteString as B 
import Data.Convertible.Base
import Data.SBV
import Data.Void
import Data.List

import Database.HDBC

--import Control.Monad (void)
import Control.Applicative (empty)
-- import Control.Monad.Combinators.Expr

import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Byte.Lexer as L
import Text.Megaparsec.Byte 


import VDB.Config
import VDB.Name
import VDB.SAT
-- import VDB.FeatureExprParser (fexpParser)


-- | Boolean expressions over features.
data FeatureExpr
   = Lit Bool
   | Ref Feature
   | Not FeatureExpr
   | And FeatureExpr FeatureExpr
   | Or  FeatureExpr FeatureExpr
  deriving (Data,Eq,Typeable,Ord)

-- | The set of features referenced in a feature expression.
features :: FeatureExpr -> Set Feature
features (Lit _)   = Set.empty
features (Ref f)   = Set.singleton f
features (Not e)   = features e
features (And l r) = features l `Set.union` features r
features (Or  l r) = features l `Set.union` features r

-- | initializes the features of a feature expr to false in a map.
--   used to initialize all features of a database, i.e. initializing
--   features of the fexp of vschema.
--   NOTE: HAVEN'T USED IT YET!!!!
-- initFeatureMap :: Boolean b => FeatureExpr -> Map Feature b
-- initFeatureMap e = Map.fromSet (\_ -> false) (features e)

-- | xor.
xor :: FeatureExpr -> FeatureExpr -> FeatureExpr
xor l r = (l `And` Not r) `Or` (Not l `And` r)

-- | disjuncts a list of fexps. Note: it doesn't shrink it!!
disjFexp :: [FeatureExpr] -> FeatureExpr
disjFexp = foldl' Or (Lit False)

-- | conjuncts a list of fexps without shrinking!!
conjFexp :: [FeatureExpr] -> FeatureExpr
conjFexp = foldl' And (Lit True)

-- | Syntactic sugar: implication
imply :: FeatureExpr -> FeatureExpr -> FeatureExpr
imply f f' = Or (Not f) f'

-- | determines if f is more general than f'.
filterFexps :: FeatureExpr -> FeatureExpr -> Bool
filterFexps f f' = tautology $ imply f f' 

-- | Evaluate a feature expression against a configuration.
evalFeatureExpr :: Boolean b => Config b -> FeatureExpr -> b
evalFeatureExpr _ (Lit b)   = if b then true else false
evalFeatureExpr c (Ref f)   = c f
evalFeatureExpr c (Not e)   = bnot (evalFeatureExpr c e)
evalFeatureExpr c (And l r) = evalFeatureExpr c l &&& evalFeatureExpr c r
evalFeatureExpr c (Or  l r) = evalFeatureExpr c l ||| evalFeatureExpr c r

-- | Select a feature within a feature expressions, potentially simplifying it.
selectFeatureExpr :: Feature -> Bool -> FeatureExpr -> FeatureExpr
selectFeatureExpr f b e = shrinkFeatureExpr (select e)
  where
    select e@(Lit _)  = e
    select e@(Ref f')
        | f == f'     = if b then true else false
        | otherwise   = e
    select (Not e)    = Not (select e)
    select (And l r)  = And (select l) (select r)
    select (Or  l r)  = Or  (select l) (select r)

-- | Pretty print a feature expression.
prettyFeatureExpr :: FeatureExpr -> String
prettyFeatureExpr = top
  where
    -- top (And l r) = sub l ++ "∧" ++ sub r
    -- top (Or  l r) = sub l ++ "∨" ++ sub r
    top (And l r) = sub l ++ " AND " ++ sub r
    top (Or  l r) = sub l ++ " OR " ++ sub r
    top e         = sub e
    -- sub (Lit b)   = if b then "#T" else "#F"
    sub (Lit b)   = if b then "TRUE" else "FALSE"

    sub (Ref f)   = featureName f
    -- sub (Not e)   = "¬" ++ sub e
    sub (Not e)   = "NOT " ++ sub e
    sub e         = "(" ++ top e ++ ")"

-- | not very pretty pretty print of a feature expression.
--   wrote it for the parser but don't need but i'm going to keep it!
prettyFeatureExpr' :: FeatureExpr -> String
prettyFeatureExpr' = top
  where
    -- top (And l r) = sub l ++ "∧" ++ sub r
    -- top (Or  l r) = sub l ++ "∨" ++ sub r
    top (And l r) = " AND " ++ sub l ++ sub r
    top (Or  l r) = " OR " ++ sub l ++ sub r
    top e         = sub e
    -- sub (Lit b)   = if b then "#T" else "#F"
    sub (Lit b)   = if b then " TRUE " else " FAlSE "

    sub (Ref f)   = featureName f
    -- sub (Not e)   = "¬" ++ sub e
    sub (Not e)   = " NOT " ++ sub e
    sub e         = " ( " ++ top e ++ " ) "


-- | Generate a symbolic predicate for a feature expression.
symbolicFeatureExpr :: FeatureExpr -> Predicate
symbolicFeatureExpr e = do
    let fs = Set.toList (features e)
    syms <- fmap (Map.fromList . zip fs) (sBools (map featureName fs))
    let look f = fromMaybe err (Map.lookup f syms)
    return (evalFeatureExpr look e)
  where err = error "symbolicFeatureExpr: Internal error, no symbol found."

-- | Reduce the size of a feature expression by applying some basic
--   simplification rules.
shrinkFeatureExpr :: FeatureExpr -> FeatureExpr
shrinkFeatureExpr e
    | unsatisfiable e           = Lit False
    | tautology e               = Lit True
shrinkFeatureExpr (Not (Not e)) = shrinkFeatureExpr e
shrinkFeatureExpr (And l r)
    | tautology l               = shrinkFeatureExpr r
    | tautology r               = shrinkFeatureExpr l
shrinkFeatureExpr (Or l r)
    | unsatisfiable l           = shrinkFeatureExpr r
    | unsatisfiable r           = shrinkFeatureExpr l
shrinkFeatureExpr e = e


{-
-- | Helper function for converting bool to bytestring
bool2ByteString :: Bool -> B.ByteString
bool2ByteString = BC.pack . show
bool2ByteString True = "True"
bool2ByteString False = "False"

-- | Helper function for converting string to bytestring
feature2ByteString :: Feature -> B.ByteString
feature2ByteString = BC.pack . featureName
-}

-- | gets a feature expression and represents it as a sqlvalue, 
--   which is constructed by the SqlByteString data constructor
-- type ConvertResult a = Either ConvertError a

sqlFeatureExp :: FeatureExpr -> ConvertResult SqlValue 
sqlFeatureExp = return . SqlByteString . BC.pack . prettyFeatureExpr
-- sqlFeatureExp (Lit b)   = return . SqlByteString $ bool2ByteString b
-- sqlFeatureExp (Ref x)   = return . SqlByteString $ feature2ByteString x
-- sqlFeatureExp (Not f)   = case sqlFeatureExp f of
--   Right (SqlByteString fsql) -> return . SqlByteString $ B.concat ["Not (", fsql, ")"]
--   _ -> Left $ ConvertError source sourceType destType msg
--     where 
--       source     = show f
--       sourceType = "FeatureExpr"
--       destType   = "SqlValue"
--       msg        = "types went wrong: is not of type FeatureExp in sqlFeatureExp"
-- sqlFeatureExp (And l r) = case (sqlFeatureExp r, sqlFeatureExp l) of
--   (Right (SqlByteString rsql), Right (SqlByteString lsql)) -> return . SqlByteString $ B.concat ["And (", rsql, " ) ", "( ", lsql, " )"]
-- sqlFeatureExp (Or l r)  = undefined

-- extractFeatureExp :: SqlValue -> Either ConvertError FeatureExpr
-- extractFeatureExp (SqlByteString s) = undefined
-- extractFeatureExp _ = Left $ ConvertError source sourceType destType msg
--    where 
--     source     = "some SqlValue"
--     sourceType = "SqlValue"
--     destType   = "FeatureExpr"
--      msg        = "types went wrong: should be SqlByteString sth"

-- sqlFeatureExp :: FeatureExpr -> ConvertResult SqlValue 
-- sqlFeatureExp = return . SqlByteString . BC.pack . prettyFeatureExpr
{-sqlFeatureExp (Lit b)   = return . SqlByteString $ bool2ByteString b
sqlFeatureExp (Ref x)   = return . SqlByteString $ feature2ByteString x
sqlFeatureExp (Not f)   = case sqlFeatureExp f of
  Right (SqlByteString fsql) -> return . SqlByteString $ B.concat ["Not (", fsql, ")"]
  _ -> Left $ ConvertError source sourceType destType msg
    where 
      source     = show f
      sourceType = "FeatureExpr"
      destType   = "SqlValue"
      msg        = "types went wrong: is not of type FeatureExp in sqlFeatureExp"
sqlFeatureExp (And l r) = case (sqlFeatureExp r, sqlFeatureExp l) of
  (Right (SqlByteString rsql), Right (SqlByteString lsql)) -> return . SqlByteString $ B.concat ["And (", rsql, " ) ", "( ", lsql, " )"]
sqlFeatureExp (Or l r)  = undefined-}

extractFeatureExp :: SqlValue -> Either ConvertError FeatureExpr
extractFeatureExp (SqlByteString s) = 
  case runParser fexpParser "" s of
    Right fexp -> Right fexp  
    _ -> Left $ ConvertError source sourceType destType msg
    where 
      source     = "some SqlValue"
      sourceType = "SqlValue"
      destType   = "FeatureExpr"
      msg        = "error in parsing the bytestring stored as fexp!!"
extractFeatureExp _ = Left $ ConvertError source sourceType destType msg
   where 
    source     = "some SqlValue"
    sourceType = "SqlValue"
    destType   = "FeatureExpr"
    msg        = "types went wrong: should be SqlByteString sth"

instance Boolean FeatureExpr where
  true  = Lit True
  false = Lit False
  bnot  = Not
  (&&&) = And
  (|||) = Or

instance SAT FeatureExpr where
  toPredicate = symbolicFeatureExpr

instance Show FeatureExpr where
  show = prettyFeatureExpr

-- safeConvert :: Convertible a b => a -> ConvertResult b
instance Convertible FeatureExpr SqlValue where
  safeConvert = sqlFeatureExp

instance Convertible SqlValue FeatureExpr where 
  safeConvert = extractFeatureExp


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


sqlval2fexp :: SqlValue -> FeatureExpr
sqlval2fexp = fromSql


fexp2sqlval :: FeatureExpr -> SqlValue
fexp2sqlval = toSql


------------------------ CONFIG 2 FEXP AND REVERSE ------------
------------------------ TODO: FILL OUT AFTER SIGMOD DEADLINE!!!

-- | generates a feature expression for the given configuration.
conf2fexp :: Config Bool -> FeatureExpr
-- Feature -> Bool -> FeatureExpr
conf2fexp c = undefined
  -- where 
  --   v = (Ref f <=> Lit b)

-- | generates a feature expr for the given list of configs.
confs2fexp :: [Config Bool] -> FeatureExpr
confs2fexp cs = undefined
-- foldl' Or (Lit False) $ conf2fexp cs

-- | extracts the valid configurations of a feature expr.
validConfsOfFexp :: FeatureExpr -> [Config Bool]
validConfsOfFexp f = undefined
  where
    fs = features f 






