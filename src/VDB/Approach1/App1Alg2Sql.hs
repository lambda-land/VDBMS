-- Approach1 translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
module VDB.Approach1.App1Alg2Sql where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import VDB.Variational

import Data.Text as T (Text, pack, append, concat)

type Vquery = Opt T.Text

trans :: Algebra -> F.FeatureExpr -> [Vquery]
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
-- trans (TRef r)      ctxt = [(ctxt, T.append "select * from " (T.pack (relationName r)))]
trans (TRef r)      ctxt = [(ctxt, T.pack (relationName r))]
trans (Empty)       ctxt = [(ctxt, "select null")]

-- | helper function for Setop queries, i.e., union, diff, prod
setAux :: SetOp -> Vquery -> Vquery -> Vquery
setAux Union = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat [l, " union ", r])
setAux Diff  = \(lo, l) (ro, r) -> ((F.And lo (F.Not ro)), T.concat [l, " minus ", r])
setAux Prod  = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat ["select * from (" , l, ") join (", r, ")"])

-- | helper function for the projection query
prjAux :: [Opt Attribute] -> Text
prjAux [(_,a)] = T.pack (attributeName a)
prjAux ((_,a):oas) = T.append (T.concat [T.pack(attributeName a), ", "]) (prjAux oas)
prjAux [] = " "

