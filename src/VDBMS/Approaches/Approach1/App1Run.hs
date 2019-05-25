-- Sends queries from approach1 translation to the db 
-- and gets the plain relational result
module VDBMS.Approaches.Approach1.App1Run where 

import VDBMS.QueryLang.Algebra
import VDBMS.VDB.Name
import VDBMS.Features.FeatureExpr.FeatureExpr 
-- import qualified VDB.Condition as C
-- import qualified VDB.Target as T
-- import VDB.Variational
-- import VDB.Type  
-- import VDB.BruteForce.BruteForceAlg2Sql
-- import VDB.BruteForce.BruteForceAppSat
-- import VDB.BruteForce.BruteForceSendQs
import VDBMS.TypeSystem (typeOfVquery')
-- import VDB.ShowVresult
import VDBMS.VDB.Schema.Schema
import VDBMS.VDB.VTable
import VDBMS.VDB.Database
import VDBMS.Approaches.Approach1.App1Alg2Sql
import VDBMS.DBMS.SqlTable

-- import Data.Map

import Database.HDBC


-- runs trans-union-filter.
runTransFilterUnion :: IConnection conn => Algebra -> PresCondAtt 
                       -> SqlDatabase conn -> IO (VTable)
runTransFilterUnion vq p vdb = do
  let sch = getSqlDBschema vdb 
      initialVarCtxt = featureModel sch 
      transQs = transVerify vq initialVarCtxt 
  res <- runVq transQs vdb -- [SqlVtable]
  let vtable = sqlVtables2VTable p res
      vtable_disjoin = updateSqlTable (disjoinDuplicate p) vtable
  -- return $ sqlVtables2VTable p res -- doesn't removes tuples with false pres cond and doesn't disjoin duplicate tuples
  return $ vtable_disjoin -- shrinks fexp, drops tuples with false fexp, disjoins duplicate tuples


-- runs trans-union-filter with static type checking.
runTransFilterUnionWithTypeChecking :: IConnection conn => Algebra -> PresCondAtt 
                       -> SqlDatabase conn -> IO (VTable)
runTransFilterUnionWithTypeChecking vq p vdb = do
  let sch = getSqlDBschema vdb 
      initialVarCtxt = featureModel sch 
  case typeOfVquery' vq initialVarCtxt sch of 
    Just tableSchema -> do 
      let transQs = transVerify vq initialVarCtxt 
      res <- runVq transQs vdb -- [SqlVtable]
      let vtable = sqlVtables2VTable p res
          vtable' = adjustVTable2TableSch tableSchema vtable
          vtable_disjoin = updateSqlTable (disjoinDuplicate p) vtable'
  -- return $ sqlVtables2VTable p res -- doesn't removes tuples with false pres cond and doesn't disjoin duplicate tuples
      return $ vtable_disjoin -- shrinks fexp, drops tuples with false fexp, disjoins duplicate tuples
    Nothing -> return $ error "the vq isn't type correct!!"
  


-- TODO: write checks, one should involve type system

