-- | Linearizes a vq to a list of opt query,
--   generates a big SQL query from the opt queries,
--   runs it over the vdb,
--   cleans up the result,
--   returns a vtable.
module VDBMS.Approaches.Linearize.RunOneBigQuery where


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra, optAlgebra)
import VDBMS.Variational.Variational 
import VDBMS.VDB.Table.Table (Table, mkVTable)
-- import VDBMS.DBMS.Table.Table (SqlTable)
-- import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable)
import VDBMS.TypeSystem.Variational.TypeSystem 
  (typeOfQuery, typeAtts, typeEnv2tableSch)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
import VDBMS.QueryLang.RelAlg.Variational.Minimization (chcSimpleReduceRec)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
-- import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
import VDBMS.QueryGen.Sql.GenSql (genSql)
import VDBMS.VDB.Table.GenTable (variantSqlTables2Table)
import VDBMS.VDB.Schema.Variational.Schema (tschFexp, tschRowType)
-- import VDBMS.Features.Config (Config)
import VDBMS.QueryGen.Sql.GenSqlSameSch (optRAQs2Sql)
import VDBMS.Approaches.Timing (timeItName)
import VDBMS.QueryLang.RelAlg.Relational.Optimization (opts_)
import VDBMS.QueryGen.RA.AddPC (addPC)
-- for testing
import VDBMS.DBsetup.Postgres.Test
import VDBMS.DBMS.Table.Table (prettySqlTable)
import VDBMS.UseCases.Test.Schema
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
runQ3_ :: Database conn => conn -> Algebra -> IO ()
runQ3_ conn vq = runQ3 conn vq >> return ()

-- |
runQ3 :: Database conn => conn -> Algebra -> IO Table
runQ3 conn vq = 
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
         type_as = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         -- try removing opt
         ra_qs = optAlgebra vsch vq_constrained_opt
         -- the following line are for optimizing the generated RA queries
         ras_opt = map (second opts_) ra_qs
         -- sql = ppSqlString $ optRAQs2Sql type_as pc ra_qs
         sql = show $ optRAQs2Sql type_as pc ras_opt
     -- putStrLn (show $ fmap snd ra_qs)
     -- putStrLn (show $ fmap snd ras_opt)
     -- putStrLn sql
     end_constQ <- getTime Monotonic
     putStrLn "constructing queries:"
     fprint (timeSpecs % "\n") start_constQ end_constQ
     sqlTab <- timeItName "running query" Monotonic $ fetchQRows conn sql
     -- putStrLn (prettySqlTable (type_as ++ pure pc) sqlTab)
     -- putStrLn (show sqlTab)
     putStrLn "gathering results: "
     strt_res <- getTime Monotonic
     let res = mkVTable type_sch sqlTab
     end_res <- getTime Monotonic
     fprint (timeSpecs % "\n") strt_res end_res
     -- timeItName "make vtable" Monotonic $ return 
     --   $ mkVTable type_sch sqlTab
     -- putStrLn (show res)
     return res

runtest :: Algebra -> IO Table
runtest q =
  do db <- tstVDBone
     runQ3 db q