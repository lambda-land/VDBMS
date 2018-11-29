-- almost smart translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
-- Note that the result returned by this approach is a
-- variational table
module VDB.VqueryTrans where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  

import Data.Text as T (Text, pack, append, concat)


trans :: Algebra -> F.FeatureExpr -> [Opt Text]
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

