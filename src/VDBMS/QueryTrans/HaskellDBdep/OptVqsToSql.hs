-- | tranlates a list of opt linearized vqueries (qs i.e.without choices)
--   to one haskelldb query. takes a list of opt linearized vq and 
--   returns ONE sql query.
module VDBMS.QueryTrans.HaskellDBdep.OptVqsToSql where 

{--
import Prelude hiding (Ordering(..))
import Data.List (nub, concat)

import qualified VDBMS.QueryLang.RelAlg.Relational.Algebra as A
import VDBMS.Variational.Opt
import VDBMS.VDB.Schema.Schema
import VDBMS.QueryTrans.Relational.AlgebraToSql

-- import qualified Database.HaskellDB as HSDB
import qualified Database.HaskellDB.PrimQuery as P

-- | creates a scheme from all primqueries in the list.
allAttributes :: [P.PrimQuery] -> P.Scheme 
allAttributes ps = nub $ concat $ map P.attributes ps


nullAttributes :: P.PrimQuery -> P.Scheme -> P.Scheme
nullAttributes = undefined


addNullAttsToPrj :: P.PrimQuery -> P.Scheme -> P.PrimQuery
addNullAttsToPrj p s = undefined
  -- where
  --   q = P.Project nullAssoc p

concatFexp :: Opt P.PrimQuery -> P.PrimQuery
concatFexp = undefined

unionAll :: [P.PrimQuery] -> P.PrimQuery
unionAll ps = undefined

transOptVqs2Sql :: [Opt A.RAlgebra] -> Schema -> P.PrimQuery
transOptVqs2Sql oqs s = unionAll prims
  where
    oprims  = mapSnd (flip transAlgebra2Sql s) oqs -- [Opt P.PrimExpr]
    allAtts = allAttributes $ map getObj oprims
    oprims' = mapSnd (flip addNullAttsToPrj allAtts) oprims
    prims   = map concatFexp oprims'

-- examples:
-- prim1 = Project [("A", AttrExpr "A")] (BaseTable "R" ["A", "B"])
-- import Database.HaskellDB.PrimQuery
-- λ> let prim1 = Project [("A", AttrExpr "A")] (BaseTable "R" ["A", "B"])
-- λ> import Database.HaskellDB.Sql.Generate
-- λ> sqlQuery prim1
-- let sql1 = defaultSqlQuery defaultSqlGenerator prim1
-- let sql1 = sqlQuery defaultSqlGenerator prim1
-- λ> ppSqlSelect sql1
-- λ> import Database.HaskellDB.PrimQuery
-- λ> import Database.HaskellDB.Sql.Generate
-- λ> let prim1 = Project [("A", AttrExpr "A")] (BaseTable "R" ["A", "B"])
-- λ> let sql1 = defaultSqlQuery defaultSqlGenerator prim1
-- λ> import Database.HaskellDB.Sql.Print
-- λ> ppSql sql1
-- λ> Database.HaskellDB.Sql.Print.ppSql sql1
-- SELECT A
-- FROM R as T1

--}