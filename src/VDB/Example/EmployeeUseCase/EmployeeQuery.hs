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

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, name, hiredate
--   FROM   otherpersonnel

empQ1_v1 :: Algebra 
empQ1_v1 = SetOp Union 
  (Proj (plainAttrs [ "empno", "name", "hiredate"]) $ TRef (Relation "v_engineerpersonnel"))
  (Proj (plainAttrs [ "empno", "name", "hiredate"]) $ TRef (Relation "v_otherpersonnel"))

-- | a query to find the titles of all jobs
--   * SELECT title FROM job;
empQ2_v1 :: Algebra
empQ2_v1 = Proj [ plainAttr "title" ] $ TRef (Relation "v_job")


-- 
-- ** Query in schema verison 2
-- 

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, name, hiredate
--   FROM   empacct
empQ1_v2 :: Algebra
empQ1_v2 = Proj (plainAttrs [ "empno", "name", "hiredate"]) $ TRef (Relation "v_empacct")

-- 
-- ** Query in schema verison 3
-- 

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, name, hiredate
--   FROM   empacct

empQ1_v3 :: Algebra
empQ1_v3 = Proj (plainAttrs [ "empno", "name", "hiredate"]) $ TRef (Relation "v_empacct")

-- 
-- ** Query in schema verison 4
-- 

-- | a query to list the employee number, employee name and employee hiredate 

--   SELECT empno, hiredate, name 
--   FROM   empacct, empbio
--   WHERE empacct.empno = empbio.empno  
empQ1_v4 :: Algebra
empQ1_v4 = let cond1 = C.Comp EQ (C.Attr (Attribute (Just (Relation "v_empacct")) "empno")) (C.Attr (Attribute (Just (Relation "v_empbio")) "empno"))
           in Proj (plainAttrs [ "empno", "name", "hiredate"]) $ Sel  cond1  $ SetOp Prod (TRef (Relation "v_empacct")) (TRef (Relation "v_empbio"))

               

-- 
-- ** Query in schema verison 5
-- 
-- | a query to list the employee number, employee name and employee hiredate 

  -- SELECT empno, firstname, lastname, hiredate 
  -- FROM   empacct, empbio
  -- WHERE empacct.empno = empbio.empno 
empQ1_v5 :: Algebra 
empQ1_v5 = Proj (plainAttrs [ "empno", "firstname","lastname", "hiredate"]) $ Sel cond1 $ SetOp Prod (TRef (Relation "v_empacct")) (TRef (Relation "v_empbio"))
         where cond1 = C.Comp EQ (C.Attr (Attribute (Just (Relation "v_empacct"))  "empno")) (C.Attr (Attribute (Just "v_empbio") "empno"))


empJoin :: Algebra
empJoin = SetOp Prod (TRef (Relation "v_empacct")) (TRef (Relation "v_empbio"))
  -- where cond1 = C.Comp EQ (C.Attr (Attribute (Just (Relation "v_empacct")) "empno")) (C.Attr (Attribute (Just (Relation "v_empbio")) "empno"))

empQ1_v4and5 :: Algebra
empQ1_v4and5 = Proj [(F.Lit True, Attribute (Just $ Relation "v_empacct") "empno"),
                     (F.And (F.Ref $ Feature "v4") (F.Not $ F.Ref $ Feature "v5"), Attribute (Just $ Relation "v_empbio") "name"),
                     (F.And (F.Not $ F.Ref $ Feature "v4") (F.Ref $ Feature "v5"), Attribute Nothing "firstname"),
                     (F.And (F.Not $ F.Ref $ Feature "v4") (F.Ref $ Feature "v5"), Attribute Nothing "lastname"),
                     (F.Lit True, Attribute Nothing "hiredate")] empJoin