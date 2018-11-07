-- | Feature expressions.
module VDB.FeatureExpr where

import Data.Data (Data,Typeable)

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.ByteString.Char8 as BC (pack)
import qualified Data.ByteString as B 
import Data.Convertible.Base
import Data.SBV

import Database.HDBC

import VDB.Config
import VDB.Name
import VDB.SAT


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

-- | Syntactic sugar: implication
imply :: FeatureExpr -> FeatureExpr -> FeatureExpr
imply f f' = Or (Not f) f'

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
    sub (Lit b)   = if b then "TRUE" else "FAlSE"

    sub (Ref f)   = featureName f
    -- sub (Not e)   = "¬" ++ sub e
    sub (Not e)   = "NOT " ++ sub e
    sub e         = "(" ++ top e ++ ")"

-- | not very pretty pretty print of a feature expression.
prettyFeatureExpr' :: FeatureExpr -> String
prettyFeatureExpr' = top
  where
    -- top (And l r) = sub l ++ "∧" ++ sub r
    -- top (Or  l r) = sub l ++ "∨" ++ sub r
    top (And l r) = "AND " ++ sub l ++ sub r
    top (Or  l r) = "OR " ++ sub l ++ sub r
    top e         = sub e
    -- sub (Lit b)   = if b then "#T" else "#F"
    sub (Lit b)   = if b then "TRUE" else "FAlSE"

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


-- | Helper function for converting bool to bytestring
-- bool2ByteString :: Bool -> B.ByteString
-- bool2ByteString = BC.pack . show
-- bool2ByteString True = "True"
-- bool2ByteString False = "False"

-- | Helper function for converting string to bytestring
-- feature2ByteString :: Feature -> B.ByteString
-- feature2ByteString = BC.pack . featureName

-- | gets a feature expression and represents it as a sqlvalue, 
--   which is constructed by the SqlByteString data constructor
-- type ConvertResult a = Either ConvertError a
sqlFeatureExp :: FeatureExpr -> ConvertResult SqlValue 
sqlFeatureExp = return . SqlByteString . BC.pack . prettyFeatureExpr'
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

extractFeatureExp :: SqlValue -> Either ConvertError FeatureExpr
extractFeatureExp (SqlByteString s) = undefined
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

