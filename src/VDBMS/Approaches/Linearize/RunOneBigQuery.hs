-- | Linearizes a vq to a list of opt query,
--   generates a big SQL query from the opt queries,
--   runs it over the vdb,
--   cleans up the result,
--   returns a vtable.
module VDBMS.Approaches.Linearize.RunOneBigQuery where


import VDBMS.VDB.Database.Database (Database(..))
import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
import VDBMS.Variational.Variational 
import VDBMS.VDB.Table.Table (Table, mkVTable)
-- import VDBMS.DBMS.Table.Table (SqlTable)
-- import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable)
import VDBMS.TypeSystem.Variational.TypeSystem (typeOfQuery, typeAtts, 
  typeEnv2tableSch)
import VDBMS.VDB.Schema.Variational.Types (featureModel)
import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
import VDBMS.QueryLang.RelAlg.Variational.Minimization (appMin)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
import VDBMS.QueryGen.Sql.GenSql (genSql)
import VDBMS.VDB.Table.GenTable (variantSqlTables2Table)
import VDBMS.VDB.Schema.Variational.Schema (tschFexp, tschRowType)
-- import VDBMS.Features.Config (Config)
import VDBMS.QueryGen.Sql.GenSqlSameSch (optRAQs2Sql)
import VDBMS.Approaches.Timing (timeItName)

-- import Control.Arrow (first, second, (***))
import Data.Bitraversable (bitraverse, bimapDefault)

import System.TimeIt
import System.Clock
import Formatting
import Formatting.Clock

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
         vq_constrained_opt = appMin vq_constrained vsch_pc vsch
         -- try removing opt
         ra_qs = optionalize_ vq_constrained_opt
         sql = ppSqlString $ optRAQs2Sql type_as pc ra_qs
     end_constQ <- getTime Monotonic
     fprint (timeSpecs % "\n") start_constQ end_constQ
     sqlTab <- timeItName "running query" Monotonic $ fetchQRows conn sql
     timeItName "make vtable" Monotonic $ return 
       $ mkVTable type_sch sqlTab

