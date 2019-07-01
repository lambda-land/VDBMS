-- | translates a variational query to a list of opt sqls.
module VDBMS.QueryTrans.HaskellDBdep.Variational.Test583 where 

{--
import VDBMS.QueryTrans.Variational.AlgebraToOptSqls
import VDBMS.VDB.Schema.Schema
import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.Variational.Opt
import VDBMS.Features.FeatureExpr.FeatureExpr 
import VDBMS.TypeSystem.TypeSystem

import Database.HaskellDB.PrimQuery 
import Database.HaskellDB.Sql.Print
-- import Database.HaskellDB.Sql.Generate 
import Database.HaskellDB.Sql.Default (defaultSqlQuery, defaultSqlGenerator)

import Text.PrettyPrint (Doc)

-- | prints a list of opt sql generated from a variational query.
--   TODO: remove shrinkFexp from here! only shrink fexp when 
--         sending the queries. don't forget to type check the queries 
--         before running them!
printSql :: Algebra -> Schema -> [Opt Doc]
printSql q s = mapFstSnd (shrinkFeatureExpr) 
                         (ppSql . (defaultSqlQuery defaultSqlGenerator)) 
                       $ trans q s 

--}