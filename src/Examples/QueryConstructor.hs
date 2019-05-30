 -- | Example Queries upon an employee data base
module Examples.QueryConstructor where

import VDBMS.QueryLang.Variational.Algebra
import qualified VDBMS.QueryLang.Variational.Condition as C
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import VDBMS.Variational.Opt
import Database.HDBC
import VDBMS.DBMS.Value.Value
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