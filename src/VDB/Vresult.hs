-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.Vresult where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
-- import VDB.Algebra
-- import VDB.Name
-- import qualified VDB.FeatureExpr as F
-- import qualified VDB.Condition as C
-- import qualified VDB.Target as T
-- import VDB.Variational
-- import VDB.Type  
-- import VDB.Schema
-- import VDB.BruteForce.BruteForceSendQs
import VDB.SqlTable (SqlVariantTable)

-- import Data.Map

-- import Database.HDBC

-- | final result that is being showed to the user
type PrettyVResult = String

-- | the one variational table that is the result of user's query.
type VResult = String

prettyVres :: VResult -> PrettyVResult
prettyVres = undefined

packVres :: [SqlVariantTable] -> VResult 
packVres = undefined
