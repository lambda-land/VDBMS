module VDBMS.QueryTrans.TestHaskellDB where 


import Database.HaskellDB.Query
import Database.HaskellDB.PrimQuery
import Database.HaskellDB.HDBRec

import Data.Set (toList)

import VDBMS.VDB.Schema.Schema
import qualified VDBMS.VDB.Name as N


instance ShowRecRow RowType where
  showRecRow r = map (\a -> (N.attributeName a,shows a)) $ toList $ getRowTypeAtts r 

emptable, jobtable :: Table RowType
emptable = Table "employee" [("id", AttrExpr "id"), ("name", AttrExpr "name")]
-- emptable = Table "employee" [("id", ConstExpr NullLit), ("name", AttrExpr "name")]
jobtable = Table "job" [("title", AttrExpr "title"), ("salary", AttrExpr "salary")]

tableEx = table emptable
tableEx2 = table jobtable

-- prjEx = do
--   t <- table emptable
--   project $ ? << t

selectEx = do
  content <- table emptable
  restrict $ Expr $ BinExpr OpEq (AttrExpr "id") (ConstExpr (IntegerLit 32))
  return content

-- WRONG!!!!!
{--
-- note: changed title to id!
SELECT id2 as id,
       salary2 as salary
FROM (SELECT id as id2,
             salary as salary2
      FROM job as T1) as T1,
     employee as T2
--}
prodEx = do 
  table emptable
  table jobtable

unionEx = union tableEx selectEx
-- unph

unionAllEx = unionAll tableEx selectEx

minusEx = minus tableEx selectEx