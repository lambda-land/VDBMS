-- | Feature expression instances. Unfortunatelly, they're all
--   orphan. But this was the only way to get rid of cyclic
--   importing of modules.
-- Question for Eric: how do I explicitly export instances?
module VDBMS.Features.FeatureExpr.Instances where

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.ByteString.Char8 as BC (pack, unpack)
import Data.Convertible.Base
import Data.SBV 

import Text.Megaparsec (runParser)

import Database.HDBC (SqlValue(..), fromSql, toSql)

import VDBMS.Features.Feature
import VDBMS.Features.FeatureExpr.Types
import VDBMS.Features.FeatureExpr.Core
import VDBMS.Features.FeatureExpr.Parser
import VDBMS.Features.SAT

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
-- prettyFeatureExpr' :: FeatureExpr -> String
-- prettyFeatureExpr' = top
--   where
--     -- top (And l r) = sub l ++ "∧" ++ sub r
--     -- top (Or  l r) = sub l ++ "∨" ++ sub r
--     top (And l r) = " AND " ++ sub l ++ sub r
--     top (Or  l r) = " OR " ++ sub l ++ sub r
--     top e         = sub e
--     -- sub (Lit b)   = if b then "#T" else "#F"
--     sub (Lit b)   = if b then " TRUE " else " FAlSE "

--     sub (Ref f)   = featureName f
--     -- sub (Not e)   = "¬" ++ sub e
--     sub (Not e)   = " NOT " ++ sub e
--     sub e         = " ( " ++ top e ++ " ) "

-- | Generate a symbolic predicate for a feature expression.
symbolicFeatureExpr :: FeatureExpr -> Predicate
symbolicFeatureExpr e = do
    let fs = Set.toList (features e)
    syms <- fmap (Map.fromList . zip fs) (sBools (map featureName fs))
    let look f = fromMaybe err (Map.lookup f syms)
    return (evalFeatureExpr look e)
  where err = error "symbolicFeatureExpr: Internal error, no symbol found."

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

-- TODO: make a type class for going back and forth
--       between sqlval and fexp!

sqlval2fexp :: SqlValue -> FeatureExpr
sqlval2fexp = fromSql


fexp2sqlval :: FeatureExpr -> SqlValue
fexp2sqlval = toSql






