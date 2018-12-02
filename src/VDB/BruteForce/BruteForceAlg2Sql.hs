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

import Data.Text as T (Text, pack, append, concat)
import Data.List (intercalate)
import Data.Maybe (catMaybes)

type Query = T.Text

-- |
bruteAlg2Sql :: Algebra -> [Config Bool] -> [Variant Bool Query]
bruteAlg2Sql = undefined


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
attName :: Opt Attribute -> Maybe String
attName (F.Lit True, a) = Just (attributeName a)
attName _             = Nothing

-- | helper function for relPrj.
attListName :: [Opt Attribute] -> [Maybe String]
attListName = map attName 

{-trans :: Algebra -> F.FeatureExpr -> [Opt Text]
trans (SetOp s l r) ctxt = [setAux s lq rq | lq <- lres, rq <- rres]
  where 
    lres = trans l ctxt
    rres = trans r ctxt
trans (Proj oas q)  ctxt = map (\(f, q') -> (f, T.concat ["select ", as, " from ", q'])) res
  where 
    res = trans q ctxt
    as  = prjAux oas 
trans (Sel c q)     ctxt = map (\(f, q') -> (f, T.concat ["select * from ", q', " where " , T.pack (show c)])) res
  where res = trans q ctxt
trans (AChc f l r)  ctxt = lres ++ rres
  where 
    lres = trans l (F.And f ctxt)
    rres = trans r (F.And (F.Not f) ctxt)
trans (TRef r)      ctxt = [(ctxt, T.append "select * from " (T.pack (relationName r)))]
trans (Empty)       ctxt = [(ctxt, "select null")]

-- | helper function for Setop queries, i.e., union, diff, prod
setAux :: SetOp -> Opt Text -> Opt Text -> Opt Text
setAux Union = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat [l, " union ", r])
setAux Diff  = \(lo, l) (ro, r) -> ((F.And lo (F.Not ro)), T.concat [l, " minus ", r])
setAux Prod  = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat ["select * from (" , l, ") join (", r, ")"])

-- | helper function for the projection query
prjAux :: [Opt Attribute] -> Text
prjAux [(o,a)] = T.pack (attributeName a)
prjAux ((o,a):oas) = T.append (T.concat [T.pack(attributeName a), ", "]) (prjAux oas)
prjAux [] = " "

-}