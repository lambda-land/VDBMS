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

-- | Translates type-correct relational algebra queries to sql queries.
--   Since the queries are type-checked before we don't need to pass the
--   schema and make sure that attributes and relations are in line with 
--   the schema.
transAlgebra2Sql :: RAlgebra -> Schema -> SqlSelect
transAlgebra2Sql (RSetOp o l r) s = undefined
transAlgebra2Sql (RProj as q)   s = undefined
transAlgebra2Sql (RSel c q)     s = undefined
transAlgebra2Sql (RJoin js)     s = undefined
transAlgebra2Sql (RProd l r rs) s = undefined
transAlgebra2Sql (RTRef r)      s = undefined
transAlgebra2Sql REmpty         s = undefined
