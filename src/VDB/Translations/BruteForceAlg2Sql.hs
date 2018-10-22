-- Brute force translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
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
-- TODO: refactor the first three cases and their helpers!!!!
bruteTrans (SetOp Union l r) = [unionBruteAux lq rq | lq <- lres, rq <- rres]
  where 
    lres = bruteTrans l
    rres = bruteTrans r
bruteTrans (SetOp Diff l r)  = [diffBruteAux lq rq | lq <- lres, rq <- rres]
  where 
    lres = bruteTrans l
    rres = bruteTrans r
bruteTrans (SetOp Prod l r)  = [prodBruteAux lq rq | lq <- lres, rq <- rres]
  where 
    lres = bruteTrans l
    rres = bruteTrans r
bruteTrans (Proj oas q)       = map (\q' -> T.concat ["select ", as, " from ", q']) res
  where 
    res = bruteTrans q
    as = prjBruteAux oas
bruteTrans (Sel c q)         = map (\q' -> T.concat ["select * from ", q', " where " , T.pack (show c)]) res
  where res = bruteTrans q
bruteTrans (AChc f l r)      = lres ++ rres
  where 
    lres = bruteTrans l
    rres = bruteTrans r
--but then I'm losing the correspondenct variation!
bruteTrans (TRef r)          = [T.append "select * from " (T.pack (relationName r))]
bruteTrans (Empty)           = ["select null"]

-- | helper function for the product query
prodBruteAux :: Text -> Text -> Text
prodBruteAux l r = T.concat ["select * from (" , l, ") join (", r, ")"]

-- | helper function for the diff query
diffBruteAux :: Text -> Text -> Text
diffBruteAux l r = T.concat [l, " minus ", r]

-- | helper function for the union query
unionBruteAux :: Text -> Text -> Text
unionBruteAux l r = T.concat [l, " union ", r]

-- | helper function for the projection query
prjBruteAux :: [Opt Attribute] -> Text
prjBruteAux ((o,a):oas) = T.append (T.concat [T.pack(attributeName a), ", "]) (prjBruteAux oas)
prjBruteAux [(o,a)] = T.pack (attributeName a)
prjBruteAux [] = " "