-- Brute force translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
-- Note that the result returned by the brute force approach is a
-- variational table
module VDB.Translations.BruteForceAlg2Sql where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
--import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  

import Database.Persist
import Database.Persist.Sqlite
import Database.Persist.Sql (rawQuery, insert)

import Data.Text as T (Text, pack, append, concat)


bruteTrans :: Algebra -> [Text]
bruteTrans (SetOp s l r) = [bruteAux s lq rq | lq <- lres, rq <- rres]
  where 
    lres = bruteTrans l
    rres = bruteTrans r
bruteTrans (Proj oas q)       = map (\q' -> T.concat ["select ", as, " from ", q']) res
  where 
    res = bruteTrans q
    as = prjBruteAux oas
bruteTrans (Sel c q)         = map (\q' -> T.concat ["select * from ", q', " where " , T.pack (show c)]) res
  where res = bruteTrans q
-- check2 --> update the pres cond clm of tuples
-- returned result? var-table or multiple relational table? var table
bruteTrans (AChc f l r)      = lres ++ rres
  where 
    lres = bruteTrans l
    rres = bruteTrans r
--but then I'm losing the correspondenct variation!
bruteTrans (TRef r)          = [T.append "select * from " (T.pack (relationName r))]
bruteTrans (Empty)           = ["select null"]

bruteAux :: SetOp -> Text -> Text -> Text
bruteAux Union l r = T.concat [l, " union ", r]
bruteAux Diff  l r = T.concat [l, " minus ", r]
bruteAux Prod  l r = T.concat ["select * from (" , l, ") join (", r, ")"]

-- | helper function for the projection query
prjBruteAux :: [Opt Attribute] -> Text
prjBruteAux [(o,a)] = T.pack (attributeName a)
prjBruteAux ((o,a):oas) = T.append (T.concat [T.pack(attributeName a), ", "]) (prjBruteAux oas)
prjBruteAux [] = " "