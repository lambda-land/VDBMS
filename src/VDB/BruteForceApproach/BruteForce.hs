-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BruteForceApproach.BruteForce where 

import VDB.Algebra
-- import VDB.Name
-- import qualified VDB.FeatureExpr as F
-- import qualified VDB.Condition as C
-- import qualified VDB.Target as T
-- import VDB.Variational
-- import VDB.Type  
-- import VDB.BruteForce.BruteForceAlg2Sql
-- import VDB.BruteForceApproach.BFConfigDB -- (applyConfigVariantTables)
-- import VDB.BruteForceApproach.BFSendQs (runBFQs)
import VDB.Translations.RelAlg2Sql (alg2Sql)
import VDB.SqlTable (SqlVariantTable)
-- import VDB.Schema
import VDB.Config
import VDB.Name
import VDB.VTable
import VDB.Database

import Database.HDBC
import Database.HDBC.Sqlite3

-- | runs a variational query for a specific list of configurations 
--   over a variational database. it returns a variational table. 
--   Note that a variational query should be run over all configs
--   that satisfy the fexp of vschema. but for now we're providing 
--   the list of config
--   HIGH PRIORITY TODO: DON'T I NEED TO CLOSE THE CONNECTION OF
--                       ALL THESE DATABASES SOMEWHERE?!?!?!?!?
--   TODO: remove the list of config and extract that from the 
--         vschema's fexp.
--   TODO: add type constraint: IConnection conn =>
--   steps:
--   1) translate vq to a list of q for each config (rel2Sql)
--      alg2Sql :: Algebra -> [Config Bool] -> [VariantQuery]
--      type VariantQuery = Variant Query Bool --> assigns config
--      type Query = Text
--   2) configure the vdb for the list of configs ()
--   3) run each q over its correspondent db ()
--   4) aggregate the result from 3 into a vtable
runBrute :: Algebra -> [Config Bool] -> PresCondAtt 
            -> DBFilePath -> SqlDatabase Connection -> IO (VTable)
runBrute vq cs p f vdb = undefined
-- do 
--   let qs = alg2Sql vq cs -- [VariantQuery]
--   dbs <- configDBall f p vdb cs -- [SqlDatabase conn]
  -- variant_result <- runSqlQsOnCorrespDBs qs dbs -- [SqlVariantTable]
  -- TODO: COMPLETE THE FOLLOWING TWO FUNCS:
  -- return $ aggregate variant_result

-- | runs brute force but returns a 
runBrute' :: Algebra -> [Config Bool] -> PresCondAtt 
            -> DBFilePath -> SqlDatabase Connection -> IO [SqlVariantTable]
runBrute' vq cs p f vdb = do
  let qs = alg2Sql vq cs -- [VariantQuery]
  dbs <- configVDBall f p vdb cs -- [SqlDatabase conn]
  runSqlQsOnCorrespDBs qs dbs -- [SqlVariantTable]

-- TODO: write checks!!!




