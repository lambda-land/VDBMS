-- | translates a variational query to a list of opt sqls.
module VDBMS.QueryTrans.Variational.Test583 where 

import VDBMS.QueryTrans.Variational.AlgebraToOptSqls
-- import VDBMS.QueryTrans.Variational.LinearizeQuery
-- import VDBMS.QueryTrans.Relational.AlgebraToSql
import VDBMS.VDB.Schema.Schema
import VDBMS.QueryLang.Variational.Algebra
-- import VDBMS.Features.Config
import VDBMS.Variational.Opt
-- import VDBMS.Variational.Variational
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import VDBMS.VDB.Name
-- import qualified VDBMS.QueryLang.Variational.Condition as C
-- import VDBMS.QueryLang.Relational.Condition

import Database.HaskellDB.PrimQuery 
import Database.HaskellDB.Sql.Print
-- import Database.HaskellDB.Sql.Generate 
import Database.HaskellDB.Sql.Default (defaultSqlQuery, defaultSqlGenerator)

import Text.PrettyPrint (Doc)

printSql :: Algebra -> Schema -> [Opt Doc]
printSql q s = mapSnd (ppSql . (defaultSqlQuery defaultSqlGenerator)) 
                    $ trans q s 

