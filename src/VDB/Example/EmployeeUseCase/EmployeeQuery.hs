 -- | Example Queries upon an employee data base
module VDB.Example.EmployeeUseCase.EmployeeQuery where

import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import Database.HDBC
import VDB.Type
import Prelude hiding (Ordering(..))
import Data.Time

--
--  ** smart contructor for plain query
--
plainAttr :: String -> Opt Attribute 
plainAttr attrName = (F.Lit True, Attribute Nothing attrName)

plainAttrs :: [String] -> [Opt Attribute]
plainAttrs []     = []
plainAttrs (x:xs) = plainAttr x : plainAttrs xs 

date2000 = SqlUTCTime $ UTCTime (fromGregorian 2000 1 1) 0
-- 
-- ** Query in schema verison 1 
-- 

-- | a query to list the employee who joined before "2000"
--   SELECT empno, name, hiredate
--   FROM   otherpersonnel
--   WHERE hiredate < ('2000-1-1')
empQ1_v1 :: Algebra 
empQ1_v1 = Proj (plainAttrs [ "empno", "name", "hiredate"]) $ Sel cond $ TRef (Relation "otherpersonnel")
         where cond = C.Comp LT (C.Attr (Attribute Nothing "hiredate")) (C.Val date2000)

-- | a query to find the titles of all jobs
--   * SELECT title FROM job;
empQ2_v1 :: Algebra
empQ2_v1 = Proj [ plainAttr "title" ] $ TRef (Relation "v_job")

-- 
-- ** Query in schema verison 2
-- 

-- | a query to list the employee who joined before "2000"
--   SELECT empno, name, hiredate
--   FROM   empacct
--   WHERE hiredate < ('2000-1-1')
empQ1_v2 :: Algebra
empQ1_v2 = Proj (plainAttrs [ "empno", "name", "hiredate"]) $ Sel cond $ TRef (Relation "empacct")
         where cond = C.Comp LT (C.Attr (Attribute Nothing "hiredate")) (C.Val date2000)

-- 
-- ** Query in schema verison 3
-- 

-- | a query to list the employee who joined before "2000"
--   SELECT empno, name, hiredate
--   FROM   empacct
--   WHERE hiredate < ('2000-1-1')
empQ1_v3 :: Algebra
empQ1_v3 = Proj (plainAttrs [ "empno", "name", "hiredate"]) $ Sel cond $ TRef (Relation "empacct")
         where cond = C.Comp LT (C.Attr (Attribute Nothing "hiredate")) (C.Val date2000)

-- 
-- ** Query in schema verison 4
-- 

-- | a query to list the employee who joined before "2000"
--   SELECT empno, hiredate, name 
--   FROM   empacct, empbio
--   WHERE empacct.empno = empbio.empno AND hiredate < ('2000-1-1') 
empQ1_v4 :: Algebra
empQ1_v4 = let cond1 = C.Comp EQ (C.Attr (Attribute (Just (Relation "empacct")) "empno")) (C.Attr (Attribute (Just (Relation "empbio")) "empno"))
               cond2 = C.Comp LT (C.Attr (Attribute Nothing "hiredate")) (C.Val date2000)
           in Proj (plainAttrs [ "empno", "name", "hiredate"]) $ Sel (C.And cond1 cond2) $ SetOp Prod (TRef (Relation "empacct")) (TRef (Relation "empbio"))

               

-- 
-- ** Query in schema verison 5
-- 
-- | a query to list the employee who joined before "2000"
  -- SELECT empno, firstname, lastname, hiredate 
  -- FROM   empacct, empbio
  -- WHERE empacct.empno = empbio.empno AND hiredate < ('2000-1-1') 
empQ1_v5 :: Algebra 
empQ1_v5 = Proj (plainAttrs [ "empno", "firstname","lastname", "hiredate"]) $ Sel cond $ SetOp Prod (TRef (Relation "empacct")) (TRef (Relation "empbio"))
         where cond = C.And cond1 cond2
               cond1 = C.Comp EQ (C.Attr (Attribute (Just (Relation "empacct"))  "empno")) (C.Attr (Attribute (Just "empbio") "empno"))
               cond2 = C.Comp LT (C.Attr (Attribute Nothing "hiredate")) (C.Val date2000)

empQ2_v5:: Algebra 
empQ2_v5 = Proj [ plainAttr "title" ] $ TRef (Relation "empacct")

