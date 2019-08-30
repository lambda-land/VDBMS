-- | generates one relational query for a given variational query without 
--   storing any temporary results.
module VDBMS.QueryGen.MySql.GenOneQ (

       genQ

) where 

import VDBMS.QueryGen.MySql.GenMulQsSameSch
import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra)
import VDBMS.QueryLang.SQL.Pure.Sql 
import VDBMS.QueryLang.SQL.Pure.Ops (updatePC)
import VDBMS.VDB.Name (Attribute, PCatt)
import VDBMS.TypeSystem.Relational.TypeSystem (RTypeEnv)
import VDBMS.Features.FeatureExpr.FeatureExpr

import Control.Arrow (first)

-- | generates a query from all queries generated with a same 
--   list of attribute.
genQ :: [Attribute] -> PCatt -> [((RAlgebra, RTypeEnv), FeatureExpr)] -> SqlSelect
genQ t p qsfs = foldr (SqlBin SqlUnionAll) (head qs) (tail qs) 
  where 
    qs = fmap (uncurry (updatePC p) . (first (genQSameSch t))) qsfs 

-- genQsSameSch :: [Attribute] -> [(RAlgebra, RTypeEnv)] -> [SqlSelect]
-- genQsSameSch as qts =
--   fmap (\(q,atts) -> adjustQSch as atts q) 
--        (fmap (transAlgebra2Sql *** rtypeEnvAtts) qts)


-- | adjusts presence conditions when combining multiple
--   queries with the same schema.
-- adjustPresCond :: [(SqlSelect, FeatureExpr)] -> PresCondAtt -> SqlSelect
-- adjustPresCond qfs p = undefined

-- | updates the queries in order to add the given feature expr 
--   to tuples presence condition.
-- updatePC :: FeatureExpr -> PresCondAtt -> SqlSelect -> SqlSelect
-- updatePC f p = undefined