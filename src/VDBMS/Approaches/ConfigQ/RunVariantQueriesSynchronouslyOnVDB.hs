-- | Configures a vq to a list of variant queries,
--   runs variant queries synchronously on the vdb,
--   filters the result,
--   gathers the filtered result in a vtable.
module VDBMS.Approaches.ConfigQ.RunVariantQueriesSynchronouslyOnVDB where 


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Variational.Variational 
import VDBMS.VDB.Table.Table (Table)
import VDBMS.TypeSystem.Variational.TypeSystem (typeOfQuery)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
import VDBMS.QueryLang.RelAlg.Variational.Minimization (appMin)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
import VDBMS.QueryGen.Sql.GenSql (genSql)

import Control.Arrow (first, second, (***))

-- |
runQ0 :: Database conn => conn -> Algebra -> IO Table
runQ0 conn vq = 
  do let vsch = schema conn
         vsch_pc = featureModel vsch
         features = dbFeatures conn
         configs = getAllConfig conn
     vq_type <- typeOfQuery vq vsch_pc vsch
     let vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = appMin vq_constrained vsch_pc vsch
         ra_qs = map (\c -> (c, configure c vq_constrained_opt)) configs
         sql_qs = fmap (second (ppSqlString . genSql . transAlgebra2Sql)) ra_qs
         sqlTables = fmap (second (fetchQRows conn)) sql_qs
     return undefined

