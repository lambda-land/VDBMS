-- Brute force translation of Variational relational algebra to SQL
module VDB.Translations.BruteForceAlg2Sql where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
--import qualified VDB.FeatureExpr as F
--import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  

import Database.Persist
import Database.Persist.Sqlite
import Database.Persist.Sql (rawQuery, insert)

import Data.Text (Text)

bruteTrans :: Algebra -> [Text]
bruteTrans (SetOp Union l r) = undefined
bruteTrans (SetOp Diff l r)  = undefined
bruteTrans (SetOp Prod l r)  = undefined
bruteTrans (Proj as q)       = undefined
bruteTrans (Sel c q)         = undefined
bruteTrans (AChc f l r)      = undefined
bruteTrans (TRef r)          = undefined
bruteTrans (Empty)           = undefined