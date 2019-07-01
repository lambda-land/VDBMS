-- | tranlates relational queries to sql.
module VDBMS.QueryTrans.AlgebraToSql (

        transAlgebra2Sql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name 
import VDBMS.QueryLang.RelAlg.Relational.Condition 
import VDBMS.QueryLang.RelAlg.Basics.SetOp
import VDBMS.VDB.Schema.Schema
-- import VDBMS.Features.SAT 

import Data.List ((\\))

-- | Translates type-correct relational algebra queries to sql queries.
--   Notes:
--   Since the queries are type-checked before we don't need to pass the
--   schema and make sure that attributes and relations are in line with 
--   the schema.
--   It just translates queries. it doesn't optimize the generated sql query.
transAlgebra2Sql :: RAlgebra -> SqlSelect
transAlgebra2Sql (RSetOp o l r) 
  = SqlBin (algBin2SqlBin o) (transAlgebra2Sql l) (transAlgebra2Sql r)
    where
      algBin2SqlBin Union = SqlUnion
      algBin2SqlBin Diff  = SqlDiff
transAlgebra2Sql (RProj as q)   
  = SqlSelect (map SqlAttr as ++ atts) (tables sql) (condition sql) (name q)
    where 
      sql = transAlgebra2Sql (thing q)
      atts = attributes sql \\ [SqlAllAtt]
transAlgebra2Sql (RSel c q)     
  = SqlSelect (attributes sql) (tables sql) (algCond2SqlCond c : condition sql) (name q)
    where 
      sql = transAlgebra2Sql (thing q)
transAlgebra2Sql (RJoin js)     
  = SqlSelect [SqlAllAtt] [constructJoinRels js] [] Nothing
transAlgebra2Sql (RProd l r rs) 
  = SqlSelect [SqlAllAtt] ([constructRel l, constructRel r] ++ map constructRel rs) [] Nothing
transAlgebra2Sql (RTRef r)      
  = SqlSelect [SqlAllAtt] [constructRel r] [] Nothing
transAlgebra2Sql REmpty         = SqlEmpty

-- | Constructs a sql relation from a rename relation.
--   Helper for transAlgebra2Sql.
constructRel :: Rename Relation -> SqlRelation
constructRel r = SqlRelation $ renameMap SqlTRef r

-- | Consructs a list of sql relaiton from joins.
--   Helper for transAlgebra2Sql.
constructJoinRels :: RJoins -> SqlRelation
constructJoinRels (RJoinTwoTable l r c) = SqlTwoTableInnerJoin l r c
constructJoinRels (RJoinMore js r c) = SqlMoreInnerJoin (constructJoinRels js) r c

-- | Translates algebra conditions to sql conditions.
--   Helper for transAlgebra2Sql.
algCond2SqlCond :: RCond RAlgebra -> RCond SqlSelect
algCond2SqlCond (RCond c) = RCond c
algCond2SqlCond (RIn a q) = RIn a (transAlgebra2Sql q)
