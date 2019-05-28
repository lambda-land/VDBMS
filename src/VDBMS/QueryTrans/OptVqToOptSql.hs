-- | tranlates linearized vqueries (qs i.e.without choices)
--   to haskelldb queries. takes a linearized vq and 
--   returns a sql query.
module VDBMS.QueryTrans.OptVqToOptSql (

        transAlgebra2Sql

) where 

import Prelude hiding (Ordering(..))

import qualified VDBMS.QueryLang.Algebra as A
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.Condition as C
import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Opt
import VDBMS.TypeSystem.TypeSystem
import VDBMS.VDB.Schema.Schema
import VDBMS.Features.SAT 

-- import qualified Database.HaskellDB as HSDB
import qualified Database.HaskellDB.PrimQuery as P
import Database.HDBC (SqlValue(..))

attListHSDB :: [Opt Attribute] -> P.Assoc 
attListHSDB as = map a2a as'
  where 
    pcIsTrue :: Opt Attribute -> Bool 
    pcIsTrue a = getFexp a == F.Lit True 
    as' = filter pcIsTrue as
    a2a :: Opt Attribute -> (P.Attribute,P.PrimExpr)
    a2a a = (aName, P.AttrExpr aName)
      where aName = attributeName $ getObj a

-- | translates operators.
--   helper for transCond2SqlCond.
vdbmsOps2hsdbOps :: CompOp -> P.BinOp
vdbmsOps2hsdbOps EQ = P.OpEq
vdbmsOps2hsdbOps NEQ = P.OpNotEq
vdbmsOps2hsdbOps LT = P.OpLt 
vdbmsOps2hsdbOps LTE = P.OpLtEq
vdbmsOps2hsdbOps GTE = P.OpGtEq
vdbmsOps2hsdbOps GT = P.OpGt

-- | translates sql values to literals.
--   helper for transCond2SqlCond.
--   TODO: complete it!!
sqlvalue2literal :: SqlValue -> P.Literal
sqlvalue2literal (SqlBool b)    = P.BoolLit b
sqlvalue2literal (SqlString s)  = P.StringLit s
sqlvalue2literal (SqlInteger i) = P.IntegerLit i 
sqlvalue2literal (SqlDouble d)  = P.DoubleLit d 
-- sqlvalue2literal (Sql) = P.DateLit c 
-- sqlvalue2literal  = P.OtherLit s

-- | translates atoms to primexpr.
--   helper for transCond2SqlCond.
atom2primExpr :: C.Atom -> P.PrimExpr
atom2primExpr (C.Val v) = P.ConstExpr $ sqlvalue2literal v
atom2primExpr (C.Attr a) = P.AttrExpr $ attributeName a

-- | translates conditions of queries to sql conditions.
--   helper for transAlgebra2Sql
transCond2SqlCond :: C.Condition -> P.PrimExpr
transCond2SqlCond (C.Lit b) = 
  P.ConstExpr $ P.BoolLit b
transCond2SqlCond (C.Comp c al ar) = 
  P.BinExpr (vdbmsOps2hsdbOps c) (atom2primExpr al) (atom2primExpr ar)
transCond2SqlCond (C.Not c) = 
  P.UnExpr P.OpNot $ transCond2SqlCond c
transCond2SqlCond (C.Or cl cr) = 
  P.BinExpr P.OpOr (transCond2SqlCond cl) (transCond2SqlCond cr)
transCond2SqlCond (C.And cl cr) =  
  P.BinExpr P.OpAnd (transCond2SqlCond cl) (transCond2SqlCond cr)
transCond2SqlCond (C.CChc _ _ _) = error "didn't expect to get choices of conditions!!"



transAlgebra2Sql :: A.Algebra -> Schema -> P.PrimQuery
transAlgebra2Sql (A.SetOp o lq rq) s = P.Binary o' lsql rsql
  where
    lsql = transAlgebra2Sql lq s 
    rsql = transAlgebra2Sql rq s
    o' = case o of
           A.Union -> P.Union
           A.Diff -> P.Difference
           A.Prod -> P.Times
transAlgebra2Sql (A.Proj as q) s = P.Project assoc sql
  where
    sql = transAlgebra2Sql q s 
    assoc = attListHSDB as
transAlgebra2Sql (A.Sel c q) s = P.Restrict c' sql
  where
    sql = transAlgebra2Sql q s
    c' = transCond2SqlCond c
transAlgebra2Sql (A.AChc _ _ _) _ = error "didn't expect to get query choices here!!"
transAlgebra2Sql (A.TRef r) s = case scheme of 
  Just sch -> P.BaseTable (relationName r) $ fmap attributeName sch
  _ -> error $ "the relation " ++ (relationName r) ++ " deons't exist in the db!!"
  where
    scheme = lookupRelAttsList r s
transAlgebra2Sql A.Empty _ = P.Empty


