 -- | Example Queries upon an employee data base
module VDB.Example.EmployeeUseCase.EmployeeQuery where

import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 


--
--  ** smart contructor for plain query
--
plainAttr :: String -> Opt Attribute 
plainAttr attrName = (F.Lit True, Attribute attrName)


-- 
-- ** Query in schema verison 1 
-- 

-- | a query to find the titles of all jobs
--   * SELECT title FROM job;
empQ1_v1 :: Algebra
empQ1_v1 = Proj [ plainAttr "title" ] $ TRef (Relation "job")




-- 
-- ** Query in schema verison 5
-- 
empQ1_v5:: Algebra 
empQ1_v5 = Proj [ plainAttr "title" ] $ TRef (Relation "empacct")

