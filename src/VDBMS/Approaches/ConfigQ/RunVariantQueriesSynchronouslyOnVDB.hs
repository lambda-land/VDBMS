-- | Configures a vq to a list of variant queries,
--   runs variant queries synchronously on the vdb,
--   filters the result,
--   gathers the filtered result in a vtable.
module VDBMS.Approaches.ConfigQ.RunVariantQueriesSynchronouslyOnVDB where 


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.VDB.Table.Table (Table)
import VDBMS.TypeSystem.Variational.TypeSystem (typeOfQuery)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)

-- |
runQ0 :: Database conn => conn -> Algebra -> IO Table
runQ0 conn vq = undefined
  -- do vq_type <- typeOfQuery vq vsch_pc vsch
  --    let vq_constrained = pushSchToQ vsch vq
  -- where
  --   vsch = schema conn
  --   vsch_pc = featureModel vsch

