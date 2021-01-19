-- | tranlates relational queries to sql.
module VDBMS.QueryTrans.AlgebraToSql (

        transAlgebra2Sql

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.VDB.Name 
import VDBMS.VDB.GenName 

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
-- transAlgebra2Sql = undefined
transAlgebra2Sql (RSetOp o l r) 
  = SqlBin (algBin2SqlBin o) (transAlgebra2Sql l) (transAlgebra2Sql r)
    where
      algBin2SqlBin Union = SqlUnion
      algBin2SqlBin Diff  = SqlDiff
-- transAlgebra2Sql (RProj as q) 
--   = SqlSelect (map (\a -> SqlAttr (renameNothing a)) as) 
--               (gentables sql)
--               (genconds sql)
--     -- SqlSelect (map SqlAttr as ++ atts) (tables sql) (condition sql) 
--     where 
--       sql = transAlgebra2Sql q
--       gentables sq 
--         | isrel sq = [renameNothing (SqlSubQuery sq)]
--         | issqlslct sq = null (attributes sq) = tables sq
--         -- | issqlop sq = error "transl rel alg to sql..unexpected prj op pattern"
--         | otherwise = [renameNothing (SqlSubQuery sq)] 
--       genconds sq 
--         | isrel sq = []
--         | null (attributes sq) = condition sq 
--         -- | issqlop sq = error "transl rel alg to sql..unexpected prj op pattern"
--         | otherwise = []
--       -- sql = thing rsql
--       -- atts = attributes sql 
--       -- \\ [SqlAllAtt]
transAlgebra2Sql (RSel c q) 
  | issqlop sql   = error "transAlgebra2Sql: unexpected sel op pattern!!"
  | issqlslct sql = SqlSelect 
    $ SelectFromWhere (sqlattributes sql) 
                      (sqltables sql) 
                      (algCond2SqlCond c : sqlconditions sql) 
  | isrel sql = SqlSelect 
    $ SelectFromWhere []
                      [renameNothing (SqlSubQuery sql)]
                      [algCond2SqlCond c]
  | otherwise = error "transAlgebra2Sql: shouldn't have got SqlEmpty!!"
    where 
      sql = transAlgebra2Sql q
transAlgebra2Sql (RJoin l r c) 
  = SqlSelect 
     $ SelectFromWhere 
         []
         [renameNothing (SqlInnerJoin (renameNothing (SqlSubQuery lsql))
                                      (renameNothing (SqlSubQuery rsql)) 
                                      c)] 
         []
    where
      lsql = transAlgebra2Sql l
      rsql = transAlgebra2Sql r
transAlgebra2Sql (RProd l r)   
  = SqlSelect $ SelectFromWhere 
                  [] 
                  [ renameNothing (SqlSubQuery lsql) 
                  , renameNothing (SqlSubQuery rsql)]
                  []
    where
      lsql =  transAlgebra2Sql l 
      rsql =  transAlgebra2Sql r
transAlgebra2Sql (RTRef r)    
  = SqlTRef r
-- transAlgebra2Sql (RRenameAlg n q) 
--   = case q of
--      (RTRef r) -> SqlSelect [] 
--                             [Rename (Just n) (SqlSubQuery (SqlTRef r))] 
--                             []
--      _         -> SqlSelect (attributes sql) 
--                             (rerename n (head (tables sql))
--                               : tail (tables sql)) 
--                             (condition sql) 
--     where
--       sql = transAlgebra2Sql q
transAlgebra2Sql REmpty         = SqlEmpty

-- | Translates algebra conditions to sql conditions.
--   Helper for transAlgebra2Sql.
algCond2SqlCond :: SqlCond RAlgebra -> SqlCond SqlSelect
algCond2SqlCond (SqlCond c)  = SqlCond c
algCond2SqlCond (SqlIn a q)  = SqlIn a (transAlgebra2Sql q)
algCond2SqlCond (SqlNot c)   = SqlNot $ algCond2SqlCond c
algCond2SqlCond (SqlOr l r)  = SqlOr (algCond2SqlCond l) (algCond2SqlCond r)
algCond2SqlCond (SqlAnd l r) = SqlAnd (algCond2SqlCond l) (algCond2SqlCond r)