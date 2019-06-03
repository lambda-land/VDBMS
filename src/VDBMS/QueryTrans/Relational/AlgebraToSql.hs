-- | tranlates relational queries to sql.
module VDBMS.QueryTrans.Relational.AlgebraToSql (

        transAlgebra2Sql

) where 

import Prelude hiding (Ordering(..))

import qualified VDBMS.QueryLang.Relational.Algebra as A
import VDBMS.VDB.Name
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.Relational.Condition as C
import VDBMS.DBMS.Value.Value
import VDBMS.Variational.Opt
import VDBMS.TypeSystem.TypeSystem
import VDBMS.VDB.Schema.Schema
import VDBMS.Features.SAT 

-- import qualified Database.HaskellDB as HSDB
import qualified Database.HaskellDB.PrimQuery as P
import Database.HDBC (SqlValue(..))

attListHSDB :: [Attribute] -> P.Assoc 
attListHSDB as = map (\a -> (attributeName a, P.AttrExpr (attributeName a))) as
  -- map a2a as'
  -- where 
  --   pcIsTrue :: Opt Attribute -> Bool 
  --   pcIsTrue a = getFexp a == F.Lit True 
  --   as' = filter pcIsTrue as
  --   a2a :: Opt Attribute -> (P.Attribute,P.PrimExpr)
  --   a2a a = (aName, P.AttrExpr aName)
  --     where aName = attributeName $ getObj a

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
sqlvalue2literal (SqlByteString s) = P.OtherLit $ show s
sqlvalue2literal (SqlWord32 s) = P.OtherLit $ show s
sqlvalue2literal (SqlWord64 s) = P.OtherLit $ show s
sqlvalue2literal (SqlInt32 s) = P.OtherLit $ show s
sqlvalue2literal (SqlInt64 s) = P.OtherLit $ show s
sqlvalue2literal (SqlChar s) = P.OtherLit $ show s
sqlvalue2literal (SqlRational s) = P.OtherLit $ show s
sqlvalue2literal (SqlLocalDate s) = P.OtherLit $ show s
sqlvalue2literal (SqlLocalTimeOfDay s) = P.OtherLit $ show s
-- sqlvalue2literal (SqlZonedLocalTimeOfDay s) = P.OtherLit $ show s
sqlvalue2literal (SqlLocalTime s) = P.OtherLit $ show s
sqlvalue2literal (SqlZonedTime s) = P.OtherLit $ show s
sqlvalue2literal (SqlUTCTime s) = P.OtherLit $ show s
sqlvalue2literal (SqlDiffTime s) = P.OtherLit $ show s
sqlvalue2literal (SqlPOSIXTime s) = P.OtherLit $ show s
sqlvalue2literal (SqlEpochTime s) = P.OtherLit $ show s
sqlvalue2literal (SqlTimeDiff s) = P.OtherLit $ show s
sqlvalue2literal SqlNull = P.NullLit
sqlvalue2literal other = error "YOU'RE DOING NON-EXHAUSTIVE PATTERN MATHCING!!"
-- sqlvalue2literal (Sql) = P.DateLit c 
-- sqlvalue2literal  = P.OtherLit s

-- | translates atoms to primexpr.
--   helper for transCond2SqlCond.
atom2primExpr :: C.Atom -> P.PrimExpr
atom2primExpr (C.Val v) = P.ConstExpr $ sqlvalue2literal v
atom2primExpr (C.Attr a) = P.AttrExpr $ attributeName a

-- | translates conditions of queries to sql conditions.
--   helper for transAlgebra2Sql
transCond2SqlCond :: C.RCondition -> P.PrimExpr
transCond2SqlCond (C.RLit b) = 
  P.ConstExpr $ P.BoolLit b
transCond2SqlCond (C.RComp c al ar) = 
  P.BinExpr (vdbmsOps2hsdbOps c) (atom2primExpr al) (atom2primExpr ar)
transCond2SqlCond (C.RNot c) = 
  P.UnExpr P.OpNot $ transCond2SqlCond c
transCond2SqlCond (C.ROr cl cr) = 
  P.BinExpr P.OpOr (transCond2SqlCond cl) (transCond2SqlCond cr)
transCond2SqlCond (C.RAnd cl cr) =  
  P.BinExpr P.OpAnd (transCond2SqlCond cl) (transCond2SqlCond cr)
-- transCond2SqlCond (C.CChc _ _ _) = error "didn't expect to get choices of conditions!!"



transAlgebra2Sql :: A.RAlgebra -> Schema -> P.PrimQuery
transAlgebra2Sql (A.RSetOp o lq rq) s = P.Binary o' lsql rsql
  where
    lsql = transAlgebra2Sql lq s 
    rsql = transAlgebra2Sql rq s
    o' = case o of
           A.Union -> P.Union
           A.Diff -> P.Difference
           A.Prod -> P.Times
transAlgebra2Sql (A.RProj as q) s = P.Project assoc sql
  where
    sql = transAlgebra2Sql q s 
    assoc = attListHSDB as
transAlgebra2Sql (A.RSel c q) s = P.Restrict c' sql
  where
    sql = transAlgebra2Sql q s
    c' = transCond2SqlCond c
-- transRelAlgebra2Sql (A.AChc _ _ _) _ = error "didn't expect to get query choices here!!"
transAlgebra2Sql (A.RTRef r) s = case scheme of 
  Just sch -> P.BaseTable (relationName r) $ fmap attributeName sch
  _ -> error $ "the relation " ++ (relationName r) ++ " deons't exist in the db!!"
  where
    scheme = lookupRelAttsList r s
transAlgebra2Sql A.REmpty _ = P.Empty


