-- | tranlates a list of opt linearized vqueries (qs i.e.without choices)
--   to one haskelldb query. takes a list of opt linearized vq and 
--   returns ONE sql query.
module VDBMS.QueryTrans.OptVqsToSql where 

import Prelude hiding (Ordering(..))

import qualified VDBMS.QueryLang.Algebra as A
-- import VDBMS.VDB.Name
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
-- import qualified VDBMS.QueryLang.Condition as C
-- import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Opt
-- import VDBMS.TypeSystem
import VDBMS.VDB.Schema.Schema
-- import VDBMS.Features.SAT 
import VDBMS.QueryTrans.OptVqToOptSql 

-- import qualified Database.HaskellDB as HSDB
import qualified Database.HaskellDB.PrimQuery as P


allAttributes :: [P.PrimQuery] -> P.Scheme 
allAttributes ps = undefined
  where
    as = nub $ map P.attributes ps

nullAttributes :: P.PrimQuery -> P.Scheme -> P.Scheme
nullAttributes = undefined

addNullAttsToPrj :: P.PrimQuery -> P.Scheme -> P.PrimQuery
addNullAttsToPrj = undefined

concatFexp :: Opt P.PrimQuery -> P.PrimQuery
concatFexp = undefined

unionAll :: [P.PrimQuery] -> P.PrimQuery
unionAll ps = undefined

transOptVqs2Sql :: [Opt A.Algebra] -> Schema -> P.PrimQuery
transOptVqs2Sql oqs s = unionAll prims
  where
    oprims  = mapSnd (flip transAlgebra2Sql s) oqs -- [Opt P.PrimExpr]
    allAtts = allAttributes $ map getObj oprims
    oprims' = mapSnd (flip addNullAttsToPrj allAtts) oprims
    prims   = map concatFexp oprims'

