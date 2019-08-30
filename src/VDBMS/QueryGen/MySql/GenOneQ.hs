-- | generates one relational query for a given variational query without 
--   storing any temporary results.
module VDBMS.QueryGen.MySql.GenOneQ (

       genQ

) where 

import VDBMS.QueryGen.MySql.GenMulQsSameSch
import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql 
import VDBMS.VDB.Name (Attribute, PresCondAtt)
import VDBMS.TypeSystem.Relational.TypeSystem (RTypeEnv)
import VDBMS.Features.FeatureExpr.FeatureExpr

-- | generates a query from all queries generated with a same 
--   list of attribute.
genQ :: [Attribute] -> [((RAlgebra, RTypeEnv), FeatureExpr)] -> SqlSelect
genQ t qsfs = undefined
	-- foldr (SqlBin SqlUnionAll) (head qs) (tail qs) 
 --  where 
 --    qs = genQsSameSch t qss 

-- | adjusts presence conditions when combining multiple
--   queries with the same schema.
adjustPresCond :: [(SqlSelect, FeatureExpr)] -> PresCondAtt -> SqlSelect
adjustPresCond qfs p = undefined

-- | updates the queries in order to add the given feature expr 
--   to tuples presence condition.
-- updatePC :: FeatureExpr -> PresCondAtt -> SqlSelect -> SqlSelect
-- updatePC f p = undefined