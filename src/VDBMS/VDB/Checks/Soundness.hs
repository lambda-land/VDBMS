-- | checks the soundness of approaches.
module VDBMS.VDB.Checks.Soundness where

-- import VDBMS.VDB.Schema.Variational.Types 
import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.VDB.Table.Table (Table, confTable)
import VDBMS.Features.Config (prettyConfig, Config)
-- import VDBMS.DBMS.Table.Table (prettySqlTable, sqltableAtts)

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

-- | soundness check 1 for all approaches.
soundnessCheck1All :: Database conn => conn -> Algebra 
                    -> IO Bool
soundnessCheck1All c q 
  = do r1 <- soundnessCheck1 c q runQ1 runQ2
       putStrLn "approach 1 VS approach 2"
       putStrLn "(var Qs VS opt Qs)"
       putStrLn "------------------------"
       putStrLn (show r1)
       r2 <- soundnessCheck1 c q runQ1 runQ3
       putStrLn "approach 1 VS approach 3"
       putStrLn "var Qs VS big"
       putStrLn "------------------------"
       putStrLn (show r2)
       r3 <- soundnessCheck1 c q runQ2 runQ3
       putStrLn "approach 2 VS approach 3"
       putStrLn "opt Qs VS big"
       putStrLn "------------------------"
       putStrLn (show r3)
       r4 <- soundnessCheck1 c q runQ1 runQ4
       putStrLn "approach 1 VS approach 4"
       putStrLn "var Qs VS cun var Qs"
       putStrLn "------------------------"
       putStrLn (show r4)
       r5 <- soundnessCheck1 c q runQ2 runQ5
       putStrLn "approach 2 VS approach 5"
       putStrLn "opt Qs VS cun opt Qs"
       putStrLn "------------------------"
       putStrLn (show r5)
       let r = and [r1,r2,r3,r4,r5]
       putStrLn "soundnessCheck1 for all approaches:"
       putStrLn (show r)
       return r

-- | soundness check 1 for all approaches on the test vdb.
soundnessCheck1AllTest :: Algebra -> IO Bool
soundnessCheck1AllTest q 
  = do db <- tstVDBone
       soundnessCheck1All db q


-- | takes a database and a query and an approach.
--   runs configured queries and configures the
--   result of the given approach and configures
--   it and then compares the two.
soundnessCheck2 :: Database conn => conn -> Algebra
                -> (conn -> Algebra -> IO Table)
                -> IO Bool
soundnessCheck2 c q app 
  = do let pc = presCond c
           confs = getAllConfig c
           features = dbFeatures c
       t <- app c q
       confedQRess <- runRelQs c q
       -- putStrLn "first print:"
       -- putStrLn ""
       -- putStrLn (show (map (\(cf,tb) -> prettyConfig features cf 
       --   ++ " : " ++ show tb) confedQRess))
       -- putStrLn "second print:"
       -- putStrLn ""
       -- putStrLn (show t)
       let confedTsApp = fmap (\cf -> (cf, confTable pc cf t)) confs
           comp :: Eq b => [(a,b)] -> [(a,b)] -> [(a,Bool)]
           comp (x:xs) (y:ys) = (fst x, (snd x == snd y)) : comp xs ys
           comp [] [] = []
           comp _ _ = error "impossible case. VDBMS.VDB.Checks.Soundness"
           -- comp' (x:xs) (y:ys) = (fst x, fst y, (snd x == snd y)) : comp' xs ys
           -- comp' [] [] = []
           compRes :: [(Config Bool, Bool)]
           compRes = comp confedQRess confedTsApp
           -- compRes' = comp' confedQRess confedTsApp
           combine ::  [(a,b)] -> [(a,b)] -> [(a,b,b)]
           combine (x:xs) (y:ys) = (fst x, snd x, snd y) : combine xs ys
           combine [] [] = []
           combine _ _ = error "impossible case. VDBMS.VDB.Checks.Soundness"
           combRes = combine confedQRess confedTsApp
           res = and $ fmap snd compRes
       -- putStrLn (show (map (\(cf1, cf2,b) -> "conf1: " 
       --   ++ prettyConfig features cf1
       --   ++ ". conf2: " 
       --   ++ prettyConfig features cf2
       --   ++ " --> "
       --   ++ show b ) compRes'))
       -- putStrLn "third print:"
       -- putStrLn ""
       -- putStrLn (show
       --   $ map (\(cf,t1,t2) -> prettyConfig features cf
       --                      ++ ". \n" 
       --                      ++ "configured query result : \n"
       --                      ++ show t1
       --                      -- ++ prettySqlTable (sqltableAtts t1) t1
       --                      ++ "configured table from approach : \n"
       --                      ++ show t2 ) 
       --         (pure $ combRes !! 2)
       --         )
       -- putStrLn "fourth print:"
       -- putStrLn ""
       -- putStrLn (show 
       --   $ map (\(cf,b) -> prettyConfig features cf 
       --                 ++ " : " ++ show b) 
       --         compRes)
       -- putStrLn ("soundnessCheck2 : " ++ show res)
       return res

-- | soundness check2 for test vdb.
soundnessCheck2Test :: Algebra -> IO Bool
soundnessCheck2Test q 
  = do db <- tstVDBone
       soundnessCheck2 db q runQ2

-- | second soundness check for all approaches.
soundnessCheck2All :: Database conn => conn -> Algebra -> IO Bool
soundnessCheck2All c q 
  = do putStrLn "app 1:"
       b1 <- soundnessCheck2 c q runQ1
       -- return b1
       putStrLn "app 2:"
       b2 <- soundnessCheck2 c q runQ2
       -- return b2
       putStrLn "app 3:"
       b3 <- soundnessCheck2 c q runQ3
       -- return b3
       putStrLn "app 4:"
       b4 <- soundnessCheck2 c q runQ4
       -- return b4
       putStrLn "app 5:"
       b5 <- soundnessCheck2 c q runQ5
       -- return b5
       putStrLn "soundness check 2 for all approaches:"
       return $ b1 && b2 && b3 && b3 && b4 && b5

-- | soundness check 2 for the test vdb.
soundnessCheck2allTest :: Algebra -> IO Bool
soundnessCheck2allTest q 
  = do db <- tstVDBone
       soundnessCheck2All db q


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

-- -- | running variant queries VS running optionalized queries 
-- --   for the test vdb.
-- varVSoptApps1test :: Algebra -> IO Bool
-- varVSoptApps1test q 
--   = do db <- tstVDBone
--        varVSoptApps1 db q

-- -- | running variant queries VS running a big query
-- --   for the test vdb.
-- varVSbigApps1test :: Algebra -> IO Bool
-- varVSbigApps1test q 
--   = do db <- tstVDBone
--        varVSbigApps1 db q 

-- -- | running optionalized queries VS running a big query
-- --   for the test vdb.
-- optVSbigApps1test :: Algebra -> IO Bool
-- optVSbigApps1test q 
--   = do db <- tstVDBone 
--        optVSbigApps1 db q 

-- -- | running cun variant queries VS running cun optionalized queries 
-- --   for the test vdb.
-- varVSoptConcurrentApps1test :: Algebra -> IO Bool
-- varVSoptConcurrentApps1test q 
--   = do db <- tstVDBone
--        varVSoptConcurrentApps1 db q 

-- -- | running variant queries VS running cun optionalized queries 
-- --   for the test vdb.
-- varVScunoptApps1test :: Algebra -> IO Bool
-- varVScunoptApps1test q 
--   = do db <- tstVDBone
--        varVScunoptApps1 db q 

-- -- | running cun variant queries VS running optionalized queries 
-- --   for the test vdb.
-- cunvarVSoptApps1test :: Algebra -> IO Bool
-- cunvarVSoptApps1test q 
--   = do db <- tstVDBone
--        cunvarVSoptApps1 db q




