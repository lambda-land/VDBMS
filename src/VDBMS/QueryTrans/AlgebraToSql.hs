-- | tranlates relational queries to sql.
module VDBMS.QueryTrans.AlgebraToSql (

        transAlgebra2Sql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name 
import VDBMS.QueryLang.SQL.Condition 
import VDBMS.QueryLang.RelAlg.Basics.SetOp
import VDBMS.VDB.Schema.Variational.Schema

import Data.List ((\\))

-- | Translates type-correct relational algebra queries to sql queries.
--   Notes:
--   Since the queries are type-checked before we don't need to pass the
--   schema and make sure that attributes and relations are in line with 
--   the schema.
--   It just translates queries. it doesn't optimize the generated sql query.
-- TODO: check it wrt renaming of attributes.
transAlgebra2Sql :: RAlgebra -> SqlSelect
transAlgebra2Sql (RSetOp o l r) 
  = SqlBin (algBin2SqlBin o) (transAlgebra2Sql l) (transAlgebra2Sql r)
    where
      algBin2SqlBin Union = SqlUnion
      algBin2SqlBin Diff  = SqlDiff
transAlgebra2Sql (RProj as q)   
  = SqlSelect (map SqlAttr as ++ atts) (tables sql) (condition sql) 
    where 
      rsql = alg2SqlWithName q
      sql = thing rsql
      atts = attributes sql \\ [SqlAllAtt]
transAlgebra2Sql (RSel c q) 
  = SqlSelect (attributes sql) (tables sql) (algCond2SqlCond c : condition sql) 
    where 
      rsql = alg2SqlWithName q 
      sql = thing rsql
transAlgebra2Sql (RJoin rl rr c) 
  = SqlSelect [SqlAllAtt] [SqlInnerJoin lsql rsql c] []
    where
      lsql = SqlSubQuery $ alg2SqlWithName rl
      rsql = SqlSubQuery $ alg2SqlWithName rr
  -- = SqlSelect [SqlAllAtt] [constructJoinRels js] [] Nothing
transAlgebra2Sql (RProd rl rr)   
  = SqlSelect [SqlAllAtt] 
              [ SqlSubQuery $ alg2SqlWithName rl
              , SqlSubQuery $ alg2SqlWithName rr]
              [] 
  -- = SqlSelect [SqlAllAtt] ([constructRel l, constructRel r] ++ map constructRel rs) [] Nothing
transAlgebra2Sql (RTRef r)      
  = SqlSelect [SqlAllAtt] [constructRel r] [] 
transAlgebra2Sql REmpty         = SqlEmpty

alg2SqlWithName :: Rename RAlgebra -> Rename SqlSelect
alg2SqlWithName = renameMap transAlgebra2Sql

-- | Constructs a sql relation from a rename relation.
--   Helper for transAlgebra2Sql.
constructRel :: Rename Relation -> SqlRelation
constructRel r = SqlSubQuery $ renameMap SqlTRef r

-- | Consructs a list of sql relaiton from joins.
--   Helper for transAlgebra2Sql.
-- constructJoinRels :: RJoins -> SqlRelation
-- constructJoinRels (RJoinTwoTable l r c) = SqlTwoTableInnerJoin l r c
-- constructJoinRels (RJoinMore js r c) = SqlMoreInnerJoin (constructJoinRels js) r c

-- | Translates algebra conditions to sql conditions.
--   Helper for transAlgebra2Sql.
algCond2SqlCond :: SqlCond RAlgebra -> SqlCond SqlSelect
algCond2SqlCond (SqlCond c)  = SqlCond c
algCond2SqlCond (SqlIn a q)  = SqlIn a (transAlgebra2Sql q)
algCond2SqlCond (SqlNot c)   = SqlNot $ algCond2SqlCond c
algCond2SqlCond (SqlOr l r)  = SqlOr (algCond2SqlCond l) (algCond2SqlCond r)
algCond2SqlCond (SqlAnd l r) = SqlAnd (algCond2SqlCond l) (algCond2SqlCond r)