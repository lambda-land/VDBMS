-- Brute force translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
module VDB.Translations.RelAlg2Sql where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import VDB.Variational
import VDB.Config  
import VDB.VqueryConfigSem
import VDB.Variant

-- import Data.Text as T (Text, pack, append, concat)
import Data.List (intercalate)
import Data.Maybe (catMaybes)

type Query = String
type VariantQuery = Variant Query Bool

-- | takes a variational query and a list of configurations
--   and returns a list of relational sql queries tagged with
--   their configuration.
alg2Sql :: Algebra -> [Config Bool] -> [VariantQuery]
alg2Sql q cs = map (variantQ q) cs 
  where
    variantQ :: Algebra -> Config Bool -> VariantQuery
    variantQ cQ c = case relTrans configuredQ of 
      Just relQ -> (relQ, c)
      _ -> error "configuring vquery went wrong!!"
      where configuredQ = configureVquery cQ c



-- | takes a vq and returns a "just text" if vq is a pure
--   relational query and returns "nothing" otherwise.
relTrans :: Algebra -> Maybe Query
relTrans (SetOp s l r) = case (relTrans l, relTrans r) of 
  (Just ql, Just qr) -> case s of 
    Prod -> Just (concat ["select * from ( ", ql, " ) join ( ", qr, " )"])
    o    -> Just (concat ["( ", ql, " ) ", show o, " ( ", qr, " )"])
  _                  -> Nothing
relTrans (Proj as q)   = case relPrj as of 
  Nothing -> Nothing
  Just [] -> Just "select null"
  Just ns -> case relTrans q of 
          Just r -> Just (concat ["select ", ns, " from ", r])
          _      -> Nothing
relTrans (Sel c q)     = case relTrans q of 
  Just r -> Just (concat ["select * from ( ", r, " ) where ", 
                            show c])
  _ -> Nothing
relTrans (AChc _ _ _)  = Nothing
relTrans (TRef r)      = Just (concat ["select * from ", (relationName r)])
relTrans Empty         = Just "select null"

-- | helper function for projecting pure relational attributes.
relPrj :: [Opt Attribute] -> Maybe String
relPrj [] = Just []
relPrj as
  | Nothing `elem` (attListName as) = Nothing
  | otherwise                       = Just (intercalate ", " (catMaybes (attListName as)))

-- | helper function for relPrj.
-- attName :: Opt Attribute -> Maybe String
-- attName (F.Lit True, a) = Just (attributeName a)
-- attName _             = Nothing

-- | helper function for relPrj.
attListName :: [Opt Attribute] -> [Maybe String]
attListName = map attName 
  where 
    attName :: Opt Attribute -> Maybe String
    attName (F.Lit True, a) = Just (attributeName a)
    attName _             = Nothing


