-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.ShowVresult where 

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

-- import Data.Map

-- import Database.HDBC

-- type ClmNameIncludedRow = [(String, SqlValue)]
-- type ClmNameIncludedTable = [ClmNameIncludedRow]
-- type RowType = [Opt (Attribute, Type)]
-- type Vresult = (RowType, ClmNameIncludedTable)

-- showVres :: Vresult -> IO Vresult
-- showVres = undefined