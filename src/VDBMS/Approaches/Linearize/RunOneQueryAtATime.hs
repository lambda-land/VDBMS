-- | Linearizes a vq to a list of opt query,
--   runs each of them on the vdb,
--   filters the results accordingly,
--   gathers the results in a vtable.
module VDBMS.Approaches.Linearize.RunOneQueryAtATime where


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Variational.Variational (Variational(..))
import VDBMS.Variational.Opt (Opt)
import VDBMS.VDB.Table.Table (Table)
import VDBMS.DBMS.Table.SqlVtable (SqlVtable)
-- import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable)
import VDBMS.TypeSystem.Variational.TypeSystem (typeOfQuery, typeEnv2tableSch)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
import VDBMS.QueryLang.RelAlg.Variational.Minimization (appMin)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
import VDBMS.QueryGen.Sql.GenSql (genSql)
import VDBMS.VDB.Table.GenTable (sqlVtables2VTable)
-- import VDBMS.VDB.Schema.Variational.Schema (tschFexp, tschRowType)
-- import VDBMS.Features.Config (Config)
import VDBMS.Approaches.Timing (timeItName)
import VDBMS.QueryLang.RelAlg.Relational.Optimization (appOpt_)

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
runQ2_ :: Database conn => conn -> Algebra -> IO ()
runQ2_ conn vq = runQ2 conn vq >> return ()

-- |
runQ2 :: Database conn => conn -> Algebra -> IO Table
runQ2 conn vq = 
  do let vsch = schema conn
         vsch_pc = featureModel vsch
         -- features = dbFeatures conn
         -- configs = getAllConfig conn
         pc = presCond conn
     vq_type <- timeItNamed "type system: " $ typeOfQuery vq vsch_pc vsch
     start_constQ <- getTime Monotonic
     let 
         -- type_pc = typePC vq_type
         type_sch = typeEnv2tableSch vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = appMin vq_constrained vsch_pc vsch
         -- try removing opt
         ra_qs = optionalize_ vq_constrained_opt
         -- the following line are for optimizing the generated RA queries
         ras_opt = map (second appOpt_) ra_qs
         -- sql_qs = fmap (bimapDefault id (ppSqlString . genSql . transAlgebra2Sql)) ra_qs
         sql_qs = fmap (bimapDefault id (ppSqlString . genSql . transAlgebra2Sql)) ras_opt
     end_constQ <- getTime Monotonic
     fprint (timeSpecs % "\n") start_constQ end_constQ
         -- try removing gensql
     let runq :: Opt String -> IO SqlVtable
         runq (f, q) = bitraverse (return . id) (fetchQRows conn) (f, q)
     sqlTables <- timeItName "running queries" Monotonic $ mapM runq sql_qs
     timeItName "gathering results" Monotonic $ return 
       $ sqlVtables2VTable pc type_sch sqlTables

