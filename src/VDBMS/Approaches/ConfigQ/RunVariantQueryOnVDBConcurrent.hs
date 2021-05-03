-- | Configures a vq to a list of variant queries,
--   runs variant query concurrently on the vdb,
--   filters the result,
--   gathers the filtered result in a vtable.
module VDBMS.Approaches.ConfigQ.RunVariantQueryOnVDBConcurrent where 


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Variational.Variational 
import VDBMS.VDB.Table.Table (Table)
-- import VDBMS.DBMS.Table.Table (SqlTable)
import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable)
import VDBMS.TypeSystem.Variational.TypeSystem 
  (typeOfQuery, typeEnv2tableSch, typeAtts)
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
-- import VDBMS.QueryGen.RA.AddPC (addPC)
-- import VDBMS.TypeSystem.Variational.InjectQualifier (injectQualifier)
-- import VDBMS.QueryLang.RelAlg.Relational.NamingScope (nameSubqRAlgebra)
-- for testing
import VDBMS.DBsetup.Postgres.Test
import VDBMS.DBMS.Table.Table (prettySqlTable)
import VDBMS.UseCases.Test.Schema
-- for testing

import Control.Arrow (first, second, (***))
import Data.Bitraversable (bitraverse, bimapDefault)

import Control.Concurrent.Async (mapConcurrently)

import System.TimeIt
import System.Clock
import Formatting
import Formatting.Clock


-- |
runQ4_ :: Database conn => IO conn -> Algebra -> IO ()
runQ4_ conn vq = runQ4 conn vq >> return ()

-- |
runQ4 :: Database conn => IO conn -> Algebra -> IO Table
runQ4 conn vq = 
  do db <- conn 
     let vsch = schema db
         vsch_pc = featureModel vsch
         features = dbFeatures db
         configs = getAllConfig db
         pc = presCond db
     vq_type <- timeItNamed "type system: " $ typeOfQuery vq vsch_pc vsch
     start_constQ <- getTime Monotonic
     let 
         -- type_pc = typePC vq_type
         type_sch = typeEnv2tableSch vq_type
         atts = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained 
         -- vq_constrained_opt_qual = injectQualifier vq_constrained_opt vsch pc
         -- try removing opt
         -- ra_qs = map (\c -> (c, configure c vq_constrained_opt)) configs --revised for the final version
         ra_qs = map (\c -> (c, configure c vq_constrained_opt)) configs
         -- ra_qs_subqNamed = map (second nameSubqRAlgebra) ra_qs
         -- the following two lines are for optimizing the generated RA queries
         -- ra_qs_schemas = map (\c -> (c, (configure c vq_constrained_opt, configure c vsch))) configs
         -- ras_opt = map (first (uncurry appOpt)) ra_qs_schemas
         -- ras_opt = map (second ((addPC pc) . opts_)) ra_qs --revised for the final version
         -- ras_opt = map (second ((addPC pc) . opts_)) ra_qs_subqNamed --dropped addpc below
         ras_opt = map (second opts_) ra_qs
         -- sql_qs = fmap (bimapDefault (ppSqlString . genSql . transAlgebra2Sql) id) ra_qs
         -- sql_qs = fmap (bimapDefault id (show . genSql . transAlgebra2Sql)) ras_opt --revised for the final version
         sql_qs = fmap (bimapDefault id (show . genSql . transAlgebra2Sql)) ras_opt
     end_constQ <- getTime Monotonic
     putStrLn "constructing queries:"
     fprint (timeSpecs % "\n") start_constQ end_constQ
         -- try removing gensql
     let runq :: (Config Bool, String) -> IO SqlVariantTable
         runq = bitraverse (return . id) (fetchQRows db) 
     sqlTables <- timeItName "running queries" Monotonic $ mapConcurrently runq sql_qs
     putStrLn "gathering results: "
     strt_res <- getTime Monotonic
     let res = variantSqlTables2Table features pc type_sch sqlTables
     end_res <- getTime Monotonic
     fprint (timeSpecs % "\n") strt_res end_res
     -- timeItName "gathering results" Monotonic $ return 
     --   $ variantSqlTables2Table features pc type_sch sqlTables
     -- putStrLn (show res)
     return res

run4test :: Algebra -> IO Table
run4test q = runQ4 tstVDBone q
