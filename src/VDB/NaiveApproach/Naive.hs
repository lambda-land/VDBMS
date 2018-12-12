-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.NaiveApproach.Naive where 

import VDB.Algebra
-- import VDB.Name
-- import qualified VDB.FeatureExpr as F
-- import qualified VDB.Condition as C
-- import qualified VDB.Target as T
-- import VDB.Variational
-- import VDB.Type  
-- import VDB.BruteForce.BruteForceAlg2Sql
import VDB.NaiveApproach.NaiveAppConfig (applyConfigVariantTables)
import VDB.NaiveApproach.NaiveSendQs (runNaiveQs)
import VDB.Translations.RelAlg2Sql (alg2Sql)
import VDB.Vresult
import VDB.SqlTable (ClmVariantTableMap)
-- import VDB.Schema
import VDB.Config
import VDB.Name

import Database.HDBC

-- | Gets a vq written in algebra with a list of configurations
--   and a variational database and returns variational results.
--   TODO: don't pass cs, instead extract it from pres cond of schema!
--   TODO: write prettyVres
--   TODO: write packVres
--   TODO: adjust types in brute force code
runNaive :: IConnection conn => Algebra -> [Config Bool] -> conn 
  -> PresCondAtt -> PrettyVResult
runNaive vq cs conn pres = undefined
{-prettyVres res
  where 
    qs = bruteAlg2Sql vq cs 
    do 
       ts <- runBruteQs qs conn 
       let tsConfiged = applyConfigVariantTables pres ts 
           res = packVres tsConfiged
       return res
-}
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











