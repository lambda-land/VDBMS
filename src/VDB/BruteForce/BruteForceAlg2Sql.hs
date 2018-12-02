-- Brute force translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
-- Note that the result returned by the brute force approach is a
-- variational table
module VDB.BruteForce.BruteForceAlg2Sql where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value
import VDB.Config  
import VDB.VqueryConfigSem

import Data.Text as T (Text, pack, append, concat)
import Data.List (intercalate)
import Data.Maybe (catMaybes)

type Query = T.Text

-- | takes a variational query and a list of configurations
--   and returns a list of relational sql queries tagged with
--   their configuration.
bruteAlg2Sql :: Algebra -> [Config Bool] -> [Variant Bool Query]
bruteAlg2Sql q cs = map (bruteQ q) cs 
  where
    bruteQ :: Algebra -> Config Bool -> Variant Bool Query
    bruteQ configuredQ c = case relTrans configuredQ of 
      Just relQ -> (c, relQ)
      _ -> error "configuring vquery went wrong!!"
      where configuredQ = configureVquery q c



-- | takes a vq and returns a "just text" if vq is a pure
--   relational query and returns "nothing" otherwise.
relTrans :: Algebra -> Maybe Query
relTrans (SetOp s l r) = case (relTrans l, relTrans r) of 
  (Just ql, Just qr) -> case s of 
    Prod -> Just (T.concat ["select * from ( ", ql, " ) join ( ", qr, " )"])
    o    -> Just (T.concat ["( ", ql, " ) ", T.pack (show o), " ( ", qr, " )"])
  _                  -> Nothing
relTrans (Proj as q)   = case relPrj as of 
  Nothing -> Nothing
  Just [] -> Just "select null"
  Just ns -> case relTrans q of 
          Just r -> Just (T.concat ["select ", T.pack ns, " from ", r])
          _      -> Nothing
relTrans (Sel c q)     = case relTrans q of 
  Just r -> Just (T.concat ["select * from ( ", r, " ) where ", 
                            T.pack (show c)])
  _ -> Nothing
relTrans (AChc _ _ _)  = Nothing
relTrans (TRef r)      = Just (T.append "select * from " (T.pack (relationName r)))
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


