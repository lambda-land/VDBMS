-- | A example schema revolution in an employee data base
module VDB.Example.EmployeeSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Value 

import qualified Data.Map as Map 

-- | schema verison 1 

--   engineerpersonnel(empno, name, hiredate, title, deptname) 
--   otherpersonnel(empno, name, hiredate, title, deptname) 
--   job(title, salary)



-- | schema version 2 

--   empacct (empno, name, hiredate, title, deptname) 
--   job (title, salary)



-- | schema version 3 

--   empacct (empno, name, hiredate, title, deptno) 
--   job (title, salary)
--   dept (deptname, deptno, managerno)



-- | schema version 4 

--   empacct (empno, hiredate, title, deptno) job (title, salary)
--   dept (deptname, deptno, managerno) empbio (empno, sex, birthdate, name)


-- | schema version 5

-- empacct (empno, hiredate, title, deptno, salary) 
-- dept (deptname, deptno, managerno)
-- empbio (empno, sex, birthdate, firstname, lastname)


