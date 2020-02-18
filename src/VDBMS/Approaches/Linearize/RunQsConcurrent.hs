-- | Linearizes a vq to a list of opt query,
--   runs them concurrently on the vdb,
--   filters the results accordingly,
--   gathers the results in a vtable.
module VDBMS.Approaches.Linearize.RunQsConcurrent where


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

-- import Control.Arrow (first, second, (***))
import Data.Bitraversable (bitraverse, bimapDefault)

import Control.Concurrent.Async (mapConcurrently)

-- |
runQ5 :: Database conn => conn -> Algebra -> IO Table
runQ5 conn vq = 
  do let vsch = schema conn
         vsch_pc = featureModel vsch
         -- features = dbFeatures conn
         -- configs = getAllConfig conn
         pc = presCond conn
     vq_type <- typeOfQuery vq vsch_pc vsch
     let 
         -- type_pc = typePC vq_type
         type_sch = typeEnv2tableSch vq_type
         vq_constrained = pushSchToQ vsch vq
         vq_constrained_opt = appMin vq_constrained vsch_pc vsch
         -- try removing opt
         ra_qs = optionalize_ vq_constrained_opt
         sql_qs = fmap (bimapDefault id (ppSqlString . genSql . transAlgebra2Sql)) ra_qs
         -- try removing gensql
         runq :: Opt String -> IO SqlVtable
         runq (f, q) = bitraverse (return . id) (fetchQRows conn) (f, q)
     sqlTables <- mapConcurrently runq sql_qs
     -- return undefined
     return $ sqlVtables2VTable pc type_sch sqlTables

