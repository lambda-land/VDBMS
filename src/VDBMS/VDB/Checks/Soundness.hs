-- | checks the soundness of approaches.
module VDBMS.VDB.Checks.Soundness where

-- import VDBMS.VDB.Schema.Variational.Types 
import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.VDB.Table.Table (Table)

import VDBMS.Approaches.ConfigQ.RunVariantQueryOnVDB 
import VDBMS.Approaches.ConfigQ.RunVariantQueryOnVDBConcurrent
import VDBMS.Approaches.Linearize.RunOneQueryAtATime
import VDBMS.Approaches.Linearize.RunQsConcurrent
import VDBMS.Approaches.Linearize.RunOneBigQuery
import VDBMS.Approaches.RunRelQ

-- import VDBMS.UseCases.Test.Schema
import VDBMS.DBsetup.Postgres.Test

-- | takes a database, query, two approaches and
--   compares if they return the same results.
soundnessCheck1 :: Database conn => conn -> Algebra 
                -> (conn -> Algebra -> IO Table)
                -> (conn -> Algebra -> IO Table)
                -> IO Bool
soundnessCheck1 c q app1 app2 
  = do t1 <- app1 c q 
       t2 <- app2 c q
       if t1 == t2 
       then return True
       else return False

-- | takes a database and a query and an approach.
--   runs configured queries and configures the
--   result of the given approach and configures
--   it and then compares the two.
soundnessCheck2 :: Database conn => conn -> Algebra
                -> (conn -> Algebra -> IO Table)
                -> IO Bool
soundnessCheck2 c q app = undefined
  -- = do t <- app c q
  --      let confs = getAllConfig c

-- | running variant queries VS running optionalized queries.
varVSoptApps1 :: Database conn => conn -> Algebra -> IO Bool
varVSoptApps1 c q = soundnessCheck1 c q runQ1 runQ2

-- | running variant queries VS running a big query.
varVSbigApps1 :: Database conn => conn -> Algebra -> IO Bool
varVSbigApps1 c q = soundnessCheck1 c q runQ1 runQ3

-- | running optionalized queries VS running a big query.
optVSbigApps1 :: Database conn => conn -> Algebra -> IO Bool
optVSbigApps1 c q = soundnessCheck1 c q runQ2 runQ3

-- | concurrently running variant queries 
--   VS cuncurrently running optionalized queries.
varVSoptConcurrentApps1 :: Database conn => conn -> Algebra -> IO Bool
varVSoptConcurrentApps1 c q = soundnessCheck1 c q runQ4 runQ5

-- | running variant queries 
--   VS cuncurrently running optionalized queries.
varVScunoptApps1 :: Database conn => conn -> Algebra -> IO Bool
varVScunoptApps1 c q = soundnessCheck1 c q runQ1 runQ5

-- | concurrently running variant queries 
--   VS running optionalized queries.
cunvarVSoptApps1 :: Database conn => conn -> Algebra -> IO Bool
cunvarVSoptApps1 c q = soundnessCheck1 c q runQ4 runQ2

-- | running variant queries VS running optionalized queries 
--   for the test vdb.
varVSoptApps1test :: Algebra -> IO Bool
varVSoptApps1test q 
  = do db <- tstVDBone
       varVSoptApps1 db q

-- | running variant queries VS running a big query
--   for the test vdb.
varVSbigApps1test :: Algebra -> IO Bool
varVSbigApps1test q 
  = do db <- tstVDBone
       varVSbigApps1 db q 

-- | running optionalized queries VS running a big query
--   for the test vdb.
optVSbigApps1test :: Algebra -> IO Bool
optVSbigApps1test q 
  = do db <- tstVDBone 
       optVSbigApps1 db q 

-- | running cun variant queries VS running cun optionalized queries 
--   for the test vdb.
varVSoptConcurrentApps1test :: Algebra -> IO Bool
varVSoptConcurrentApps1test q 
  = do db <- tstVDBone
       varVSoptConcurrentApps1 db q 

-- | running variant queries VS running cun optionalized queries 
--   for the test vdb.
varVScunoptApps1test :: Algebra -> IO Bool
varVScunoptApps1test q 
  = do db <- tstVDBone
       varVScunoptApps1 db q 

-- | running cun variant queries VS running optionalized queries 
--   for the test vdb.
cunvarVSoptApps1test :: Algebra -> IO Bool
cunvarVSoptApps1test q 
  = do db <- tstVDBone
       cunvarVSoptApps1 db q




