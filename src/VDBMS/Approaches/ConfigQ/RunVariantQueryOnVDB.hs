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
-- for testing

import Control.Arrow (first, second, (***))
import Data.Bitraversable (bitraverse, bimapDefault)

import System.TimeIt
import System.Clock
import Formatting
import Formatting.Clock


-- |
runQ1_ :: Database conn => IO conn -> Algebra -> IO ()
runQ1_ conn vq = runQ1_ conn vq >> return ()

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
         -- type_pc = typePC vq_type
         type_sch = typeEnv2tableSch vq_type
         atts = typeAtts vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = chcSimpleReduceRec vq_constrained
         -- vq_constrained_opt_qual = injectQualifier vq_constrained_opt vsch pc
         -- try removing opt
         ra_qs = map (\c -> (c, configure c vq_constrained_opt)) configs --revised for the final version
         -- ra_qs = map (\c -> (c, configure c vq_constrained_opt_qual)) configs
         -- ra_qs_subqNamed = map (second nameSubqRAlgebra) ra_qs
         -- the following two lines are for optimizing the generated RA queries
         -- ra_qs_schemas = map (\c -> ((configure c vq_constrained_opt, configure c vsch), c)) configs
         -- ras_opt = map (first (uncurry appOpt)) ra_qs_schemas
         -- ras_opt = map (second ((addPC pc) . opts_)) ra_qs --dropped addpc below
         ras_opt = map (second opts_) ra_qs
         -- sql_qs = fmap (bimapDefault (ppSqlString . genSql . transAlgebra2Sql) id) ra_qs
         -- sql_qs = fmap (bimapDefault id (show . genSql . transAlgebra2Sql)) ras_opt -- testing gensql. uncomment below after test
         sql_qs = fmap (bimapDefault id (ppSqlString . (fixPC pc) . genSql . transAlgebra2Sql)) ras_opt --revised for the final version
         -- sql_qs = fmap (bimapDefault id (show . transAlgebra2Sql)) ras_opt --revised for the final version
         -- sql_qs = fmap (bimapDefault id (show . transAlgebra2Sql)) ras_opt
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
         -- try removing gensql
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
     end_res <- getTime Monotonic
     fprint (timeSpecs % "\n") strt_res end_res
     -- timeItName "gathering results" Monotonic $ return 
     --   $ variantSqlTables2Table features pc type_sch sqlTables
     -- putStrLn (show res)
     return res

-- testfetch q = 
--   do db <- tstVDBone
--      fetchQRows db q

run1test :: Algebra -> IO Table
run1test = runQ1 tstVDBone

run1emp :: Algebra -> IO Table
run1emp = runQ1 employeeVDB

-- -- |
-- runQ1test :: Database conn => conn -> Algebra -> IO [(String, Config Bool)]
-- runQ1test conn vq =
--   do let vsch = schema conn
--          vsch_pc = featureModel vsch
--          features = dbFeatures conn
--          configs = getAllConfig conn
--          pc = presCond conn
--      vq_type <- timeItNamed "type system" $ typeOfQuery vq vsch_pc vsch
--      start_constQ <- getTime Monotonic
--      let 
--          -- type_pc = typePC vq_type
--          type_sch = typeEnv2tableSch vq_type
--          vq_constrained = pushSchToQ vsch vq
--          vq_constrained_opt = chcSimpleReduceRec vq_constrained
--          -- try removing opt
--          ra_qs = map (\c -> (configure c vq_constrained_opt, c)) configs
--          -- the following two lines are for optimizing the generated RA queries
--          -- ra_qs_schemas = map (\c -> ((configure c vq_constrained_opt, configure c vsch), c)) configs
--          -- ras_opt = map (first (uncurry appOpt)) ra_qs_schemas
--          ras_opt = map (first opts_) ra_qs
--          -- sql_qs = fmap (bimapDefault (ppSqlString . genSql . transAlgebra2Sql) id) ra_qs
--          sql_qs = fmap (bimapDefault (show . genSql . transAlgebra2Sql) id) ras_opt
--      end_constQ <- getTime Monotonic
--      fprint (timeSpecs % "\n") start_constQ end_constQ
--      return sql_qs

-- runtestqs :: Algebra -> IO String
-- runtestqs q =
--   do tstvdb <- tstVDBone
--      qs <- runQ1test tstvdb q
--      return $ head $ mapM fst qs
