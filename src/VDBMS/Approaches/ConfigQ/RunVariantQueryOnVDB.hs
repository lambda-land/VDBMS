-- | Configures a vq to a list of variant queries,
--   runs each variant query on the vdb,
--   filters the result,
--   gathers the filtered result in a vtable.
module VDBMS.Approaches.ConfigQ.RunVariantQueryOnVDB where 


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Variational.Variational 
import VDBMS.VDB.Table.Table (Table)
-- import VDBMS.DBMS.Table.Table (SqlTable)
import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable, ppSqlVarTab)
import VDBMS.TypeSystem.Variational.TypeSystem (typeOfQuery, typeEnv2tableSch, typeAtts)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
import VDBMS.QueryLang.RelAlg.Variational.Minimization (chcSimpleReduceRec)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
-- import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
import VDBMS.QueryGen.Sql.GenSql (genSql)
import VDBMS.VDB.Table.GenTable (variantSqlTables2Table)
-- import VDBMS.VDB.Schema.Variational.Schema (tschFexp, tschRowType)
import VDBMS.Features.Config (Config)
import VDBMS.Approaches.Timing (timeItName)
import VDBMS.QueryLang.RelAlg.Relational.Optimization (opts_)
-- import VDBMS.QueryLang.SQL.Pure.Sql (ppSqlString)
-- for testing
import VDBMS.DBsetup.Postgres.Test
-- for testing

import Control.Arrow (first, second, (***))
import Data.Bitraversable (bitraverse, bimapDefault)

import System.TimeIt
import System.Clock
import Formatting
import Formatting.Clock

-- Clock data type
-- Monotonic: a monotonic but not-absolute time which never changes after start-up.
-- Realtime: an absolute Epoch-based time (which is the system clock and can change).
-- ProcessCPUTime: CPU time taken by the process.
-- ThreadCPUTime: CPU time taken by the thread.

-- |
runQ1_ :: Database conn => conn -> Algebra -> IO ()
runQ1_ conn vq = runQ1_ conn vq >> return ()

-- |
runQ1 :: Database conn => conn -> Algebra -> IO Table
runQ1 conn vq = 
  do let vsch = schema conn
         vsch_pc = featureModel vsch
         features = dbFeatures conn
         configs = getAllConfig conn
         pc = presCond conn
     vq_type <- timeItNamed "type system: " $ typeOfQuery vq vsch_pc vsch
     start_constQ <- getTime Monotonic
     let 
         -- type_pc = typePC vq_type
         type_sch = typeEnv2tableSch vq_type
         atts = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         -- try removing opt
         ra_qs = map (\c -> (configure c vq_constrained_opt, c)) configs
         -- the following two lines are for optimizing the generated RA queries
         -- ra_qs_schemas = map (\c -> ((configure c vq_constrained_opt, configure c vsch), c)) configs
         -- ras_opt = map (first (uncurry appOpt)) ra_qs_schemas
         ras_opt = map (first opts_) ra_qs
         -- sql_qs = fmap (bimapDefault (ppSqlString . genSql . transAlgebra2Sql) id) ra_qs
         sql_qs = fmap (bimapDefault (show . genSql . transAlgebra2Sql) id) ras_opt
     end_constQ <- getTime Monotonic
     fprint (timeSpecs % "\n") start_constQ end_constQ
     putStrLn (show $ fmap fst ra_qs)
     putStrLn (show $ fmap fst ras_opt)
     putStrLn (show $ fmap fst sql_qs)
         -- try removing gensql
     let runq :: (String, Config Bool) -> IO SqlVariantTable
         runq (q, c) = bitraverse (fetchQRows conn) (return . id) (q, c)
     sqlTables <- timeItName "running queries" Monotonic $ mapM runq sql_qs
     -- putStrLn (show (length sqlTables))
     -- putStrLn (ppSqlVarTab features atts (sqlTables !! 4))
     -- putStrLn (show (map (ppSqlVarTab features atts) sqlTables))
     timeItName "gathering results" Monotonic $ return 
       $ variantSqlTables2Table features pc type_sch sqlTables

testfetch q = 
  do db <- tstVDBone
     fetchQRows db q

-- runtest :: Algebra -> IO Table
runtest q =
  do db <- tstVDBone
     runQ1 db q

-- |
runQ1test :: Database conn => conn -> Algebra -> IO [(String, Config Bool)]
runQ1test conn vq =
  do let vsch = schema conn
         vsch_pc = featureModel vsch
         features = dbFeatures conn
         configs = getAllConfig conn
         pc = presCond conn
     vq_type <- timeItNamed "type system" $ typeOfQuery vq vsch_pc vsch
     start_constQ <- getTime Monotonic
     let 
         -- type_pc = typePC vq_type
         type_sch = typeEnv2tableSch vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         -- try removing opt
         ra_qs = map (\c -> (configure c vq_constrained_opt, c)) configs
         -- the following two lines are for optimizing the generated RA queries
         -- ra_qs_schemas = map (\c -> ((configure c vq_constrained_opt, configure c vsch), c)) configs
         -- ras_opt = map (first (uncurry appOpt)) ra_qs_schemas
         ras_opt = map (first opts_) ra_qs
         -- sql_qs = fmap (bimapDefault (ppSqlString . genSql . transAlgebra2Sql) id) ra_qs
         sql_qs = fmap (bimapDefault (show . genSql . transAlgebra2Sql) id) ras_opt
     end_constQ <- getTime Monotonic
     fprint (timeSpecs % "\n") start_constQ end_constQ
     return sql_qs

runtestqs :: Algebra -> IO String
runtestqs q =
  do tstvdb <- tstVDBone
     qs <- runQ1test tstvdb q
     return $ head $ mapM fst qs
