-- Applies the sat solver to the result of queries sent to the db
module VDB.BruteForce.BruteForceAppSat where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  

import Database.Persist
import Database.Persist.Sqlite
import Database.Persist.Sql (rawQuery, insert)

import Data.Text as T (Text, pack, append, concat)

{--
bruteTrans :: Algebra -> F.FeatureExpr -> [Opt Text]
bruteTrans (SetOp s l r) ctxt = [bruteAux s lq rq | lq <- lres, rq <- rres]
  where 
    lres = bruteTrans l ctxt
    rres = bruteTrans r ctxt
bruteTrans (Proj oas q)  ctxt = map (\(f, q') -> (f, T.concat ["select ", as, " from ", q'])) res
  where 
    res = bruteTrans q ctxt
    as  = prjBruteAux oas 
bruteTrans (Sel c q)     ctxt = map (\(f, q') -> (f, T.concat ["select * from ", q', " where " , T.pack (show c)])) res
  where res = bruteTrans q ctxt
bruteTrans (AChc f l r)  ctxt = lres ++ rres
  where 
    lres = bruteTrans l (F.And f ctxt)
    rres = bruteTrans r (F.And (F.Not f) ctxt)
bruteTrans (TRef r)      ctxt = [(ctxt, T.append "select * from " (T.pack (relationName r)))]
bruteTrans (Empty)       ctxt = [(ctxt, "select null")]

-- | helper function for Setop queries, i.e., union, diff, prod
bruteAux :: SetOp -> Opt Text -> Opt Text -> Opt Text
bruteAux Union = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat [l, " union ", r])
bruteAux Diff  = \(lo, l) (ro, r) -> ((F.And lo (F.Not ro)), T.concat [l, " minus ", r])
bruteAux Prod  = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat ["select * from (" , l, ") join (", r, ")"])

-- | helper function for the projection query
prjBruteAux :: [Opt Attribute] -> Text
prjBruteAux [(o,a)] = T.pack (attributeName a)
prjBruteAux ((o,a):oas) = T.append (T.concat [T.pack(attributeName a), ", "]) (prjBruteAux oas)
prjBruteAux [] = " 

--}