-- Sends queries from approach1 translation to the db 
-- and gets the plain relational result
module VDB.Approach1.App1Run where 

import VDB.Algebra
import VDB.Name
import VDB.FeatureExpr 
-- import qualified VDB.Condition as C
-- import qualified VDB.Target as T
-- import VDB.Variational
-- import VDB.Type  
-- import VDB.BruteForce.BruteForceAlg2Sql
-- import VDB.BruteForce.BruteForceAppSat
-- import VDB.BruteForce.BruteForceSendQs
-- import VDB.TypeSystem.Semantics
-- import VDB.ShowVresult
import VDB.Schema
import VDB.VTable
import VDB.Database
import VDB.Approach1.App1Alg2Sql
import VDB.SqlTable

-- import Data.Map

import Database.HDBC


-- runs trans-union-filter.
runTransFilterUnion :: IConnection conn => Algebra -> PresCondAtt 
                       -> SqlDatabase conn -> IO (VTable)
runTransFilterUnion vq p vdb = do
  let initialVarCtxt = featureModel $ getSqlDBschema vdb 
      transQs = trans vq initialVarCtxt
  res <- runVq transQs vdb -- [SqlVtable]
  let vtable = sqlVtables2VTable p res
      vtable_disjoin = updateSqlTable (disjoinDuplicate p) vtable
  -- return $ sqlVtables2VTable p res -- doesn't removes tuples with false pres cond and doesn't disjoin duplicate tuples
  return $ vtable_disjoin -- shrinks fexp, drops tuples with false fexp, disjoins duplicate tuples



-- TODO: write checks, one should involve type system

