 -- | Example Queries upon an employee data base
module Examples.EmployeeUseCase.EmployeeQuery where

import qualified VDBMS.QueryLang.RelAlg.Variational.Algebra as A
-- import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import VDBMS.Variational.Variational 
import Database.HDBC
import VDBMS.DBMS.Value.Value
import Prelude hiding (Ordering(..))
import Data.Time
import Examples.QueryConstructor


date2000 = SqlUTCTime $ UTCTime (fromGregorian 2000 1 1) 0
-- 
-- ** Query in schema verison 1 
-- 

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, name, hiredate
--   FROM   otherpersonnel

empQ1_v1 :: A.Algebra 
empQ1_v1 = A.SetOp A.Union 
  (A.Proj (plainAttrs [ "empno", "name", "hiredate"]) $ A.TRef (Relation "v_engineerpersonnel"))
  (A.Proj (plainAttrs [ "empno", "name", "hiredate"]) $ A.TRef (Relation "v_otherpersonnel"))

-- | a query to find the titles of all jobs
--   * SELECT title FROM job;
empQ2_v1 :: A.Algebra
empQ2_v1 = A.Proj [ plainAttr "title" ] $ A.TRef (Relation "v_job")


-- 
-- ** Query in schema verison 2
-- 

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, name, hiredate
--   FROM   empacct
empQ1_v2 :: A.Algebra
empQ1_v2 = A.Proj (plainAttrs [ "empno", "name", "hiredate"]) $ A.TRef (Relation "v_empacct")

-- 
-- ** Query in schema verison 3
-- 

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, name, hiredate
--   FROM   empacct

empQ1_v3 :: A.Algebra
empQ1_v3 = A.Proj (plainAttrs [ "empno", "name", "hiredate"]) $ A.TRef (Relation "v_empacct")

-- 
-- ** Query in schema verison 4
-- 

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, hiredate, name 
--   FROM   empacct, empbio
--   WHERE empacct.empno = empbio.empno  
empQ1_v4 :: A.Algebra
empQ1_v4 = let cond1 = A.Comp EQ (A.Attr (Attribute "empno")) (A.Attr (Attribute "empno"))
           in A.Proj (plainAttrs [ "empno", "name", "hiredate"]) $ A.Sel  cond1  $ A.SetOp A.Prod (A.TRef (Relation "v_empacct")) (A.TRef (Relation "v_empbio"))

               

-- 
-- ** Query in schema verison 5
-- 
-- | a query to list the employee number, employee name and employee hiredate 

  -- SELECT empno, firstname, lastname, hiredate 
  -- FROM   empacct, empbio
  -- WHERE empacct.empno = empbio.empno 
empQ1_v5 :: A.Algebra 
empQ1_v5 = A.Proj (plainAttrs [ "empno", "firstname","lastname", "hiredate"]) $ A.Sel cond1 $ A.SetOp A.Prod (A.TRef (Relation "v_empacct")) (A.TRef (Relation "v_empbio"))
         where cond1 = A.Comp EQ (A.Attr (Attribute  "empno")) (A.Attr (Attribute "empno"))


empJoin :: A.Algebra
empJoin = A.SetOp A.Prod (A.TRef (Relation "v_empacct")) (A.TRef (Relation "v_empbio"))
  -- where cond1 = A.Comp EQ (A.Attr (Attribute (Just (Relation "v_empacct")) "empno")) (A.Attr (Attribute (Just (Relation "v_empbio")) "empno"))

empQ1_v4and5 :: A.Algebra
empQ1_v4and5 = A.Proj [(F.Lit True, Attribute "empno"),
                     (F.And (F.Ref $ F.Feature "v4") (F.Not $ F.Ref $ F.Feature "v5"), Attribute "name"),
                     (F.And (F.Not $ F.Ref $ F.Feature "v4") (F.Ref $ F.Feature "v5"), Attribute "firstname"),
                     (F.And (F.Not $ F.Ref $ F.Feature "v4") (F.Ref $ F.Feature "v5"), Attribute "lastname"),
                     (F.Lit True, Attribute "hiredate")] empJoin