 -- | Example Queries upon an employee data base
module Example.QueryConstructor where

import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import Database.HDBC
import VDB.Type
import Prelude hiding (Ordering(..))
import Data.Time

--
--  ** smart contructor for plain query
--
plainAttr :: String -> Opt Attribute 
plainAttr attrName = (F.Lit True, Attribute Nothing attrName)

plainAttrs :: [String] -> [Opt Attribute]
plainAttrs []     = []
plainAttrs (x:xs) = plainAttr x : plainAttrs xs 