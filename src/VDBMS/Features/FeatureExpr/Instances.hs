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

-- | extracts/reads a feature expr from a sqlvalue
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

-- | Less than equal for feature expressions.
leFexp :: FeatureExpr -> FeatureExpr -> Bool
leFexp (Lit False) r           = True
leFexp (Lit True)  (Lit False) = False
leFexp (Lit b)     r           = True
leFexp l           (Lit b)     = False
leFexp (Ref v)     r           = True
leFexp l           (Ref v)     = False
leFexp (And l r)   (And l' r') = leFexp l l' && leFexp r r'
leFexp lf          (And l r)   = False
leFexp (Or l r)    (Or l' r')  = leFexp l l' && leFexp r r'


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

instance Eq FeatureExpr where
  l == r = equivalent l r

instance Ord FeatureExpr where
 (<=) = leFexp

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






