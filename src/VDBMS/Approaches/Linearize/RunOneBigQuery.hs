-- | Linearizes a vq to a list of opt query,
--   generates a big SQL query from the opt queries,
--   runs it over the vdb,
--   cleans up the result,
--   returns a vtable.
module VDBMS.Approaches.Linearize.RunOneBigQuery where


-- import VDBMS.VDB.Database.Database (Database(..))
-- import VDBMS.QueryLang.RelAlg.Variational.Algebra (Algebra)
-- import VDBMS.Variational.Variational 
-- import VDBMS.VDB.Table.Table (Table)
-- -- import VDBMS.DBMS.Table.Table (SqlTable)
-- import VDBMS.DBMS.Table.SqlVariantTable (SqlVariantTable)
-- import VDBMS.TypeSystem.Variational.TypeSystem (typeOfQuery, typePC, typeEnv2tableSch)
-- import VDBMS.VDB.Schema.Variational.Types (featureModel)
-- import VDBMS.QueryGen.VRA.PushSchToQ (pushSchToQ)
-- import VDBMS.QueryLang.RelAlg.Variational.Minimization (appMin)
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
-- import VDBMS.QueryGen.MySql.PrintSql (ppSqlString)
-- import VDBMS.QueryGen.Sql.GenSql (genSql)
-- import VDBMS.VDB.Table.GenTable (variantSqlTables2Table)
-- import VDBMS.VDB.Schema.Variational.Schema (tschFexp, tschRowType)
-- import VDBMS.Features.Config (Config)

-- -- import Control.Arrow (first, second, (***))
-- import Data.Bitraversable (bitraverse, bimapDefault)

-- -- |
-- runQ3 :: Database conn => conn -> Algebra -> IO Table
-- runQ3 conn vq = 
--   do let vsch = schema conn
--          vsch_pc = featureModel vsch
--          features = dbFeatures conn
--          configs = getAllConfig conn
--          pc = presCond conn
--      vq_type <- typeOfQuery vq vsch_pc vsch
--      let type_pc = typePC vq_type
--          type_sch = typeEnv2tableSch vq_type
--          vq_constrained = pushSchToQ vsch vq
--          vq_constrained_opt = appMin vq_constrained vsch_pc vsch
--          -- try removing opt
--          ra_qs = map (\c -> (configure c vq_constrained_opt, c)) configs
--          sql_qs = fmap (bimapDefault (ppSqlString . genSql . transAlgebra2Sql) id) ra_qs
--          -- try removing gensql
--          runq :: (String, Config Bool) -> IO SqlVariantTable
--          runq (q, c) = bitraverse (fetchQRows conn) (return . id) (q, c)
--      sqlTables <- mapM runq sql_qs
--      return $ variantSqlTables2Table features pc type_sch sqlTables

