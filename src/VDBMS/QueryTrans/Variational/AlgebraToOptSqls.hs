-- | translates a variational query to a list of opt sqls.
module VDBMS.QueryTrans.Variational.AlgebraToOptSqls (

        trans

) where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.QueryTrans.Relational.AlgebraToSql
import VDBMS.VDB.Schema.Schema
import VDBMS.Variational.Opt
import VDBMS.Variational.Variational

import Database.HaskellDB.PrimQuery 

-- | translates a variational query to a list of sql queries.
trans :: Algebra -> Schema -> [Opt PrimQuery]
trans q s = mapSnd (flip transAlgebra2Sql s) validQs
  where
    linearizedQs = linearize q
    validQs = validifyOpts linearizedQs


-- Martin's idea: send this concurrently instead of making them into
-- one query