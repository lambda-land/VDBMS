-- | generates one relational query for a given variational query without 
--   storing any temporary results.
module VDBMS.QueryGen.MySql.GenOneQ (

       genQ

) where 

import VDBMS.QueryGen.MySql.GenMulQsSameSch (genQSameSch)
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
