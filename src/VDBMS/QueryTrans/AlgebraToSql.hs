-- | tranlates relational queries to sql.
module VDBMS.QueryTrans.AlgebraToSql where 


-- (

--         transAlgebra2Sql

-- ) where 

-- import Prelude hiding (Ordering(..))

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
-- import VDBMS.VDB.Name
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import qualified VDBMS.QueryLang.RelAlg.Relational.Condition as C
-- import VDBMS.DBMS.Value.Value
-- import VDBMS.Variational.Opt
-- import VDBMS.TypeSystem.TypeSystem
import VDBMS.VDB.Schema.Schema
-- import VDBMS.Features.SAT 

-- import Database.HDBC (SqlValue(..))

transAlgebra2Sql :: RAlgebra -> Schema -> SqlSelect
transAlgebra2Sql = undefined
