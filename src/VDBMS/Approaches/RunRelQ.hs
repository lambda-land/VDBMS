-- | runs relaitonal sql queries on the vdb. 
module VDBMS.Approaches.RunRelQ where 


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Variational.Variational 
import VDBMS.VDB.Table.Table (Table)
-- import VDBMS.DBMS.Table.Table (SqlTable)
import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable, prettySqlVarTab)
import VDBMS.TypeSystem.Variational.TypeSystem 
  (typeOfQuery, typeEnv2tableSch, typeAtts, typePC)
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
import VDBMS.QueryGen.RA.AddPC (addPC)
import VDBMS.DBMS.Table.Table (SqlTable, configSqlTable)
-- import VDBMS.QueryLang.SQL.Pure.Sql (ppSqlString)
-- for testing
import VDBMS.DBsetup.Postgres.Test
import VDBMS.DBMS.Table.Table (prettySqlTable)
import VDBMS.UseCases.Test.Schema
-- for testing

import Control.Arrow (first, second, (***))
import Data.Bitraversable (bitraverse, bimapDefault)

-- | runs relaitonal sql queries on the vdb. 
runRelQ :: Database conn => conn -> Config Bool -> Algebra -> IO SqlTable
runRelQ conn c vq = 
  do let vsch = schema conn
         vsch_pc = featureModel vsch
         features = dbFeatures conn
         configs = getAllConfig conn
         pc = presCond conn
         q = (show . genSql . transAlgebra2Sql . (addPC pc) . opts_) 
             (configure c 
               (chcSimpleReduceRec (pushSchToQ vsch vq)))
     tab <- fetchQRows conn q
     vq_type <- typeOfQuery vq vsch_pc vsch
     let tab' = configSqlTable c (typePC vq_type) pc tab
     return tab'

-- | runs all configured queries of a variational query
--   on a VDB.
runRelQs :: Database conn => conn -> Algebra -> IO [(Config Bool, SqlTable)]
runRelQs conn q =
  do let configs = getAllConfig conn
         runq :: (Config Bool, Algebra) -> IO (Config Bool, SqlTable)
         runq (c, vq) = bitraverse (return . id) (runRelQ conn c) (c, vq)
     ts <- mapM runq $ fmap (\cf -> (cf, q)) configs
     return ts