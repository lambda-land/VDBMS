-- | Linearizes a vq to a list of opt query,
--   runs each of them on the vdb,
--   filters the results accordingly,
--   gathers the results in a vtable.
module VDBMS.Approaches.Linearize.RunOneQueryAtATime where


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra, optAlgebra)
import VDBMS.Variational.Variational (Variational(..))
import VDBMS.Variational.Opt (Opt)
import VDBMS.VDB.Table.Table (Table, getSqlTable)
import VDBMS.DBMS.Table.SqlVtable (SqlVtable, prettySqlVTable)
import VDBMS.QueryLang.SQL.Pure.Sql (ppSqlString)
-- import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable)
import VDBMS.TypeSystem.Variational.TypeSystem 
  (typeOfQuery, typeEnv2tableSch, typeAtts)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
import VDBMS.QueryLang.RelAlg.Variational.Minimization (chcSimpleReduceRec)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
-- import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
import VDBMS.QueryGen.Sql.GenSql (genSql)
import VDBMS.VDB.Table.GenTable (sqlVtables2VTable)
-- import VDBMS.VDB.Schema.Variational.Schema (tschFexp, tschRowType)
-- import VDBMS.Features.Config (Config)
import VDBMS.Approaches.Timing (timeItName)
import VDBMS.QueryLang.RelAlg.Relational.Optimization (opts_)
import VDBMS.QueryGen.Sql.FixPC (fixPC)
-- import VDBMS.QueryGen.RA.AddPC (addPC)
-- import VDBMS.TypeSystem.Variational.InjectQualifier (injectQualifier)
-- import VDBMS.QueryLang.RelAlg.Relational.NamingScope (nameSubqRAlgebra)
-- for testing
import VDBMS.DBsetup.Postgres.Test
import VDBMS.DBMS.Table.Table (prettySqlTable)
import VDBMS.UseCases.Test.Schema
import VDBMS.DBsetup.Postgres.EmployeeDB
import VDBMS.DBsetup.Postgres.EnronEmailDB
-- for testing

import Control.Arrow (first, second, (***))
import Data.Bitraversable (bitraverse, bimapDefault)

import System.TimeIt
import System.Clock
import Formatting
import Formatting.Clock


-- |
runQ2_ :: Database conn => IO conn -> Algebra -> IO ()
-- runQ2_ conn vq = runQ2 conn vq >> return ()
runQ2_ conn vq =
  do db <- conn
     let vsch = schema db
         vsch_pc = featureModel vsch
         pc = presCond db
     vq_type <- timeItNamed "type system: " $ typeOfQuery vq vsch_pc vsch
     start_constQ <- getTime Monotonic
     let type_sch = typeEnv2tableSch vq_type
         atts = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         ra_qs = optAlgebra vsch vq_constrained_opt
         ras_opt = map (second opts_) ra_qs
         sql_qs = fmap (bimapDefault id (ppSqlString . (fixPC pc) . genSql . transAlgebra2Sql)) ras_opt
     end_constQ <- getTime Monotonic
     putStrLn "constructing queries:"
     fprint (timeSpecs % "\n") start_constQ end_constQ
     -- putStrLn (show $ fmap snd ra_qs)
     -- putStrLn (show $ fmap snd ras_opt)
     -- putStrLn (show $ fmap snd sql_qs)
     let runq :: Opt String -> IO SqlVtable
         runq = bitraverse (return . id) (fetchQRows db) 
     sqlTables <- timeItName "running queries" Monotonic $ mapM runq sql_qs
     -- putStrLn (show (length sqlTables))
     -- putStrLn (prettySqlVTable (atts ++ [pc]) (sqlTables !! 0))
     putStrLn "gathering results: "
     strt_res <- getTime Monotonic
     let res = sqlVtables2VTable pc type_sch sqlTables
         lres = length (getSqlTable res)
     putStrLn (show lres)
     end_res <- getTime Monotonic
     fprint (timeSpecs % "\n") strt_res end_res
     -- timeItName "gathering results" Monotonic $ return 
     --   $ sqlVtables2VTable pc type_sch sqlTables
     -- putStrLn (show res)
     return ()

-- |
runQ2 :: Database conn => IO conn -> Algebra -> IO Table
runQ2 conn vq = 
  do db <- conn
     let vsch = schema db
         vsch_pc = featureModel vsch
         pc = presCond db
     vq_type <- timeItNamed "type system: " $ typeOfQuery vq vsch_pc vsch
     start_constQ <- getTime Monotonic
     let type_sch = typeEnv2tableSch vq_type
         atts = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         ra_qs = optAlgebra vsch vq_constrained_opt
         ras_opt = map (second opts_) ra_qs
         sql_qs = fmap (bimapDefault id (ppSqlString . (fixPC pc) . genSql . transAlgebra2Sql)) ras_opt
     end_constQ <- getTime Monotonic
     putStrLn "constructing queries:"
     fprint (timeSpecs % "\n") start_constQ end_constQ
     -- putStrLn (show $ fmap snd ra_qs)
     -- putStrLn (show $ fmap snd ras_opt)
     -- putStrLn (show $ fmap snd sql_qs)
     let runq :: Opt String -> IO SqlVtable
         runq = bitraverse (return . id) (fetchQRows db) 
     sqlTables <- timeItName "running queries" Monotonic $ mapM runq sql_qs
     -- putStrLn (show (length sqlTables))
     -- putStrLn (prettySqlVTable (atts ++ [pc]) (sqlTables !! 0))
     putStrLn "gathering results: "
     strt_res <- getTime Monotonic
     let res = sqlVtables2VTable pc type_sch sqlTables
         lres = length (getSqlTable res)
     putStrLn (show lres)
     end_res <- getTime Monotonic
     fprint (timeSpecs % "\n") strt_res end_res
     -- timeItName "gathering results" Monotonic $ return 
     --   $ sqlVtables2VTable pc type_sch sqlTables
     -- putStrLn (show res)
     return res

run2test :: Algebra -> IO Table
run2test = runQ2 tstVDBone

run2emp :: Algebra -> IO ()
run2emp = runQ2_ employeeVDB

run2emp' :: Algebra -> IO Table
run2emp' = runQ2 employeeVDB

run2en :: Algebra -> IO ()
run2en = runQ2_ enronVDB

run2en' :: Algebra -> IO Table
run2en' = runQ2 enronVDB


