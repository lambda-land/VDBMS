-- | tranlates relational queries to sql.
module VDBMS.QueryTrans.AlgebraToSql (

        transAlgebra2Sql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name 

import Data.List ((\\))

-- | Translates type-correct relational algebra queries to sql queries.
--   Notes:
--   Since the queries are type-checked before we don't need to pass the
--   schema and make sure that attributes and relations are in line with 
--   the schema.
--   It just translates queries. it doesn't optimize the generated sql query.
--  You could possibly add qualifier where ever possible in this step!
--  Sth to keep in mind if things go wrong!!
transAlgebra2Sql :: RAlgebra -> SqlSelect
transAlgebra2Sql (RSetOp o l r) 
  = SqlBin (algBin2SqlBin o) (transAlgebra2Sql l) (transAlgebra2Sql r)
    where
      algBin2SqlBin Union = SqlUnion
      algBin2SqlBin Diff  = SqlDiff
transAlgebra2Sql (RProj as q) = undefined
  -- = SqlSelect (map SqlAttr as ++ atts) (tables sql) (condition sql) 
  --   where 
  --     sql = transAlgebra2Sql q
  --     -- sql = thing rsql
  --     atts = attributes sql 
  --     -- \\ [SqlAllAtt]
transAlgebra2Sql (RSel c q) = undefined
  -- = SqlSelect (attributes sql) (tables sql) (algCond2SqlCond c : condition sql) 
  --   where 
  --     rsql = alg2SqlWithName q 
  --     sql = thing rsql
transAlgebra2Sql (RJoin rl rr c) = undefined
  -- = SqlSelect latts [SqlInnerJoin (SqlSubQuery lsql) (SqlSubQuery rsql) c] []
  --   where
  --     lsql =  alg2SqlWithName rl
  --     rsql = alg2SqlWithName rr
  --     latts = (attributes . thing) lsql
  --     -- ratts = (attributes . thing) rsql
transAlgebra2Sql (RProd rl rr)   = undefined
  -- = SqlSelect (latts ++ ratts) 
  --             [ SqlSubQuery lsql, SqlSubQuery rsql]
  --             []
  --   where
  --     lsql =  alg2SqlWithName rl 
  --     rsql =  alg2SqlWithName rr
  --     latts = (attributes . thing) lsql
  --     ratts = (attributes . thing) rsql
transAlgebra2Sql (RTRef r)     = undefined
  -- = SqlSelect [] [constructRel r] [] 
transAlgebra2Sql (RRenameAlg q n) = undefined
transAlgebra2Sql REmpty         = SqlEmpty

-- | Attaches the name of a relational alg query to its equiv
--   sql query.
alg2SqlWithName :: Rename RAlgebra -> Rename SqlSelect
alg2SqlWithName = renameMap transAlgebra2Sql

-- | Constructs a sql relation from a rename relation.
--   Helper for transAlgebra2Sql.
constructRel :: Rename Relation -> SqlRelation
constructRel r = SqlSubQuery $ renameMap SqlTRef r

-- | Translates algebra conditions to sql conditions.
--   Helper for transAlgebra2Sql.
algCond2SqlCond :: SqlCond RAlgebra -> SqlCond SqlSelect
algCond2SqlCond (SqlCond c)  = SqlCond c
algCond2SqlCond (SqlIn a q)  = SqlIn a (transAlgebra2Sql q)
algCond2SqlCond (SqlNot c)   = SqlNot $ algCond2SqlCond c
algCond2SqlCond (SqlOr l r)  = SqlOr (algCond2SqlCond l) (algCond2SqlCond r)
algCond2SqlCond (SqlAnd l r) = SqlAnd (algCond2SqlCond l) (algCond2SqlCond r)