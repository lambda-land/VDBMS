-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BruteForce.BruteForce where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
import VDB.BruteForce.BruteForceAlg2Sql
import VDB.BruteForce.BruteForceAppConfig
import VDB.BruteForce.BruteForceSendQs
import VDB.TypeSystem.Semantics
import VDB.ShowVresult
import VDB.Schema

import Data.Map

import Database.HDBC


-- steps of brute force approach:
-- 1. get a list of configuration, apply them to a vq


-- | 
runBrute :: IConnection conn => Algebra -> [Config Bool] -> conn -> PresCondAttName -> [ClmVariantTableMap]

-- 1. initialize vctxt to the pres cond of vsch
-- 2. translate the vq to sql qs *bruteTrans*
-- 3. get conn to db and run *runBruteQsClm* to run sql qs from trans 
-- 4. apply sat solver to vtables *checkSatAllVtables*
-- 5. show results as one vtable


-- type ClmNameIncludedRow = [(String, SqlValue)]
-- type ClmNameIncludedTable = [ClmNameIncludedRow]
-- type RowType = [Opt (Attribute, Type)]
-- type Vresult = (RowType, ClmNameIncludedTable)


-- step1:

-- | set the variational context at the beginning
--   to the presence condition of the v-schema
--
-- initialVarCtxt :: Schema -> VariationalContext
-- initialVarCtxt (f,_) = f


-- brute :: IConnection conn => Algebra -> Schema -> conn -> Vresult
-- brute vq s c = undefined
{-  where 
  	initialVarCtxt :: Schema -> VariationalContext
  	initialVarCtxt (f,_) = f
    vctxt = initialVarCtxt s 
    qs = bruteTrans vq vctxt 
    do vts <- runBruteQsClm qs c 
    return vts 
    checkSatAllVtables :: [(ClmNameIncludedVtable, Vctxt)] -> PresCondAttName -> [ClmNameIncludedVtable]
    checkSatAllVtables 
-}











