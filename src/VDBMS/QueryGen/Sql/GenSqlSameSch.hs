-- | generates one sql query from sql queries/ra queries with different schemas
module VDBMS.QueryGen.Sql.GenSqlSameSch (

       optRAQs2Sql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql (SqlSelect(..), SqlBinOp(..), isSqlEmpty)
-- import VDBMS.TypeSystem.Relational.TypeSystem (RTypeEnv, rtypeEnvAtts)
import VDBMS.VDB.Name (Attribute, PCatt)
import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.QueryLang.SQL.Pure.Ops
import VDBMS.Variational.Opt (Opt, mapSnd)

import Debug.Trace

-- | takes a list of opt RA queries and generate one sql query.
optRAQs2Sql :: [Attribute] -> PCatt -> [Opt RAlgebra] -> SqlSelect
optRAQs2Sql as pc qs = trace ("debugin: " ++ show sqls ++ "updated: " 
  ++ show (tail (reverse sqls_updatedPC_sameSch)))
  $ foldl (SqlBin SqlUnionAll) 
          (head sqls_updatedPC_sameSch) 
          (tail sqls_updatedPC_sameSch)
    where
      sqls = mapSnd transAlgebra2Sql qs
      sqls_updatedPC_sameSch = map 
        (\(f,q) -> updatePC pc (adjustQSch as (sqlQAtts q) q) f) 
        (filter (not . isSqlEmpty . snd) sqls)

