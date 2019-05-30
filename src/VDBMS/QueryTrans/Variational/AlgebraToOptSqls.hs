-- | translates a variational query to a list of opt sqls.
module VDBMS.QueryTrans.Variational.AlgebraToOptSqls (

        trans

) where 

import VDBMS.QueryLang.Variational.Algebra
import VDBMS.QueryTrans.Variational.LinearizeQuery
import VDBMS.QueryTrans.Relational.AlgebraToSql
import VDBMS.VDB.Schema.Schema
-- import VDBMS.QueryLang.Relational.Algebra
-- import VDBMS.Features.Config
import VDBMS.Variational.Opt
-- import VDBMS.Variational.Variational
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import VDBMS.VDB.Name
-- import qualified VDBMS.QueryLang.Variational.Condition as C
-- import VDBMS.QueryLang.Relational.Condition

import Database.HaskellDB.PrimQuery 

-- | translates a variational query to a list of sql queries.
trans :: Algebra -> Schema -> [Opt PrimQuery]
trans q s = mapSnd (flip transAlgebra2Sql s) validQs
  where
    linearizedQs = linearize q
    validQs = validifyOpts linearizedQs


-- Martin's idea: send this concurrently instead of making them into
-- one query