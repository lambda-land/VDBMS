-- | Configures a vq to a list of variant queries,
--   runs each variant query on the vdb,
--   filters the result,
--   gathers the filtered result in a vtable.
module VDBMS.Approaches.ConfigQ.RunVariantQueryOnVDB where 


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
-- import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra(..))
import VDBMS.Variational.Variational 
import VDBMS.VDB.Table.Table (Table, getSqlTable)
-- import VDBMS.DBMS.Table.Table (SqlTable)
import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable, prettySqlVarTab)
import VDBMS.TypeSystem.Variational.TypeSystem 
  (typeOfQuery, typeEnv2tableSch, typeAtts)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
import VDBMS.QueryLang.RelAlg.Variational.Minimization (chcSimpleReduceRec)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
-- import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
import VDBMS.QueryLang.SQL.Pure.Sql (ppSqlString)
import VDBMS.QueryGen.Sql.GenSql (genSql)
import VDBMS.VDB.Table.GenTable (variantSqlTables2Table)
-- import VDBMS.VDB.Schema.Variational.Schema (tschFexp, tschRowType)
import VDBMS.Features.Config (Config)
import VDBMS.Approaches.Timing (timeItName)
import VDBMS.QueryLang.RelAlg.Relational.Optimization (opts_)
-- import VDBMS.QueryGen.RA.AddPC (addPC)
import VDBMS.QueryGen.Sql.FixPC (fixPC)
-- import VDBMS.TypeSystem.Variational.InjectQualifier (injectQualifier)
-- import VDBMS.QueryLang.RelAlg.Relational.NamingScope (nameSubqRAlgebra)
-- import VDBMS.QueryLang.SQL.Pure.Sql (ppSqlString)
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
runQ1_ :: Database conn => IO conn -> Algebra -> IO ()
runQ1_ conn vq = 
  do db <- conn
     let vsch = schema db
         vsch_pc = featureModel vsch
         features = dbFeatures db
         configs = getAllConfig db
         pc = presCond db
     -- vq_type <- timeItNamed "type system: " $ typeOfQuery vq vsch_pc vsch
     vq_type <- typeOfQuery vq vsch_pc vsch
     -- putStrLn (show vq_type)
     start_constQ <- getTime Monotonic
     let type_sch = typeEnv2tableSch vq_type
         atts = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         ra_qs = map (\c -> (c, configure c vq_constrained_opt)) configs 
         ras_opt = map (second opts_) ra_qs
         sql_qs = fmap (bimapDefault id (ppSqlString . (fixPC pc) . genSql . transAlgebra2Sql)) ras_opt 
     -- putStrLn (show type_sch)
     -- putStrLn ("vq_constrained " ++ show vq_constrained)
     -- putStrLn ("vq_constrained_opt " ++ show vq_constrained_opt)
     -- putStrLn (show )
     -- end_constQ <- getTime Monotonic
     -- putStrLn ("explicitly anntoted query: " ++ show vq_constrained_opt) 
     -- putStrLn "constructing queries:"
     -- fprint (timeSpecs % "\n") start_constQ end_constQ
     -- putStrLn (show $ fmap snd ra_qs)
     -- putStrLn (show $ fmap snd ras_opt)
     -- putStrLn (show $ numVar ra_qs)
     -- putStrLn (show $ fmap snd sql_qs)
     let runq :: (Config Bool, String) -> IO SqlVariantTable
         runq = bitraverse (return . id) (fetchQRows db) 
     -- sqlTables <- timeItName "running queries" Monotonic $ mapM runq sql_qs
     sqlTables <- mapM runq sql_qs
     -- putStrLn (show (length sqlTables))
     -- tabtest <- fetchQRows conn ((map fst sql_qs) !! 1)
     -- tabtest <- fetchQRows conn "select * from r1;"
     -- putStrLn (show tabtest)
     -- putStrLn (prettySqlTable [aone_, atwo_, pc] tabtest)
     -- putStrLn (prettySqlVarTab features (atts ++ [pc]) (sqlTables !! 2))
     -- putStrLn (show (map (ppSqlVarTab features atts) sqlTables))
     -- putStrLn "gathering results: "
     -- strt_res <- getTime Monotonic
     let res = variantSqlTables2Table features pc type_sch sqlTables
         lres = length (getSqlTable res)
     putStrLn (show lres)
     end_res <- getTime Monotonic
     fprint (timeSpecs % "\n") start_constQ end_res
     -- fprint (timeSpecs % "\n") strt_res end_res
     -- timeItName "gathering results" Monotonic $ return 
     --   $ variantSqlTables2Table features pc type_sch sqlTables
     return ()

-- numVar :: [(a, RAlgebra)] -> Int 
-- numVar ras = length $ filter (/=REmpty) (map snd ras)

-- |
runQ1 :: Database conn => IO conn -> Algebra -> IO Table
runQ1 conn vq = 
  do db <- conn
     let vsch = schema db
         vsch_pc = featureModel vsch
         features = dbFeatures db
         configs = getAllConfig db
         pc = presCond db
     vq_type <- timeItNamed "type system: " $ typeOfQuery vq vsch_pc vsch
     -- putStrLn (show vq_type)
     start_constQ <- getTime Monotonic
     let 
         type_sch = typeEnv2tableSch vq_type
         atts = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         ra_qs = map (\c -> (c, configure c vq_constrained_opt)) configs 
         ras_opt = map (second opts_) ra_qs
         sql_qs = fmap (bimapDefault id (ppSqlString . (fixPC pc) . genSql . transAlgebra2Sql)) ras_opt 
     -- putStrLn (show type_sch)
     -- putStrLn ("vq_constrained " ++ show vq_constrained)
     -- putStrLn ("vq_constrained_opt " ++ show vq_constrained_opt)
     -- putStrLn (show )
     end_constQ <- getTime Monotonic
     -- putStrLn ("explicitly anntoted query: " ++ show vq_constrained_opt) 
     putStrLn "constructing queries:"
     fprint (timeSpecs % "\n") start_constQ end_constQ
     -- putStrLn (show $ fmap snd ra_qs)
     -- putStrLn (show $ fmap snd ras_opt)
     putStrLn (show $ fmap snd sql_qs)
     let runq :: (Config Bool, String) -> IO SqlVariantTable
         runq = bitraverse (return . id) (fetchQRows db) 
     sqlTables <- timeItName "running queries" Monotonic $ mapM runq sql_qs
     -- putStrLn (show (length sqlTables))
     -- tabtest <- fetchQRows conn ((map fst sql_qs) !! 1)
     -- tabtest <- fetchQRows conn "select * from r1;"
     -- putStrLn (show tabtest)
     -- putStrLn (prettySqlTable [aone_, atwo_, pc] tabtest)
     -- putStrLn (prettySqlVarTab features (atts ++ [pc]) (sqlTables !! 2))
     -- putStrLn (show (map (ppSqlVarTab features atts) sqlTables))
     putStrLn "gathering results: "
     strt_res <- getTime Monotonic
     let res = variantSqlTables2Table features pc type_sch sqlTables
         lres = length (getSqlTable res)
     putStrLn (show lres)
     end_res <- getTime Monotonic
     fprint (timeSpecs % "\n") strt_res end_res
     -- timeItName "gathering results" Monotonic $ return 
     --   $ variantSqlTables2Table features pc type_sch sqlTables
     return res


run1test :: Algebra -> IO Table
run1test = runQ1 tstVDBone

run1emp :: Algebra -> IO ()
run1emp = runQ1_ employeeVDB

run1emp' :: Algebra -> IO Table
run1emp' = runQ1 employeeVDB

run1en :: Algebra -> IO ()
run1en = runQ1_ enronVDB

run1en' :: Algebra -> IO Table
run1en' = runQ1 enronVDB

