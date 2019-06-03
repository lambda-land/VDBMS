 -- | An example schema revolution in an employee data base
module Examples.EmployeeUseCase.EmployeeSchema where

import VDBMS.VDB.Schema.Schema
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
import VDBMS.DBMS.Value.Value
-- import VDBMS.Variational

import qualified Data.Map as M 
import Examples.SmartConstructor(constructRelMap, constructRowType)

-- 
-- Features
-- 

empv1 = Ref (Feature "v1")
empv2 = Ref (Feature "v2")
empv3 = Ref (Feature "v3")
empv4 = Ref (Feature "v4")
empv5 = Ref (Feature "v5")

-- 
-- Relations
-- 

engineerpersonnel, otherpersonnel, job, dept, empacct, empbio :: Relation
engineerpersonnel = Relation "v_engineerpersonnel"
otherpersonnel    = Relation "v_otherpersonnel"
job               = Relation "v_job"
dept              = Relation "v_dept"
empacct           = Relation "v_empacct"
empbio            = Relation "v_empbio"

-- 
-- Attributes
-- 

empno, name, hiredate, title, deptname, salary :: Attribute
deptno, managerno, sex, birthdate, firstname, lastname :: Attribute
empno     = genAtt "empno"
name      = genAtt "name"
hiredate  = genAtt "hiredate"
title     = genAtt "title"
deptname  = genAtt "deptname"
salary    = genAtt "salary"
deptno    = genAtt "deptno"
managerno = Attribute (Just dept) "managerno"
sex       = Attribute (Just empbio) "sex"
firstname = Attribute (Just empbio) "firstname"
lastname  = Attribute (Just empbio) "lastname"
birthdate = Attribute (Just empbio) "birthdate"

--  
--  ** schema verison 1 
--  

empSchema1 :: Schema 
empSchema1 = ( empv1, constructRelMap [ ( engineerpersonnel,  engineerpersonnel_v1)
                                                   , ( otherpersonnel,    otherpersonnel_v1)
                                                   , ( job,  job_v1234)
                                                   ]
             )

-- |  engineerpersonnel(empno, name, hiredate, title, deptname) 
engineerpersonnel_v1 :: [(Attribute,SqlType)]
engineerpersonnel_v1 = [ (addEng empno, TInt32), 
                         (addEng name,  TString)
                       , (addEng hiredate, TUTCTime)
                       , (addEng title,  TString)
                       , (addEng deptname, TString)
                       ]
  where 
    addEng = flip addRelToAtt engineerpersonnel

-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: [(Attribute,SqlType)]
otherpersonnel_v1 =  [ (addOther empno,TInt32)
                     , (addOther name, TString)
                     , (addOther hiredate, TUTCTime)
                     , (addOther title, TString)
                     , (addOther deptname, TString)
                     ]
  where 
    addOther = flip addRelToAtt otherpersonnel

-- | job(title, salary)
job_v1234 ::[(Attribute,SqlType)]
job_v1234 = [ (addJob title, TString)
          , (addJob salary,  TInt32)
          ]
  where 
    addJob = flip addRelToAtt job

-- 
-- ** schema version 2 
-- 

empSchema2 :: Schema 
empSchema2 = (empv2, constructRelMap [ ( empacct, empacct_v2)
                                                  , (job,  job_v1234)
                                                  ] 
              )


-- |  empacct (empno, name, hiredate, title, deptname) 
empacct_v2 :: [(Attribute,SqlType)]
empacct_v2 =  [ (addEmpacct empno,    TInt32)
              , (addEmpacct name,     TString)
              , (addEmpacct hiredate, TUTCTime)
              , (addEmpacct title,    TString)
              , (addEmpacct deptname, TString)
              ]
  where 
    addEmpacct = flip addRelToAtt empacct

--
--  ** schema version 3 
-- 

empSchema3 :: Schema
empSchema3 = (empv3,  constructRelMap   [ (empacct,  empacct_v3)
                                                     , ( job,  job_v1234)
                                                     , ( dept,  dept_v345)
                                                     ]
              )

-- | empacct (empno, name, hiredate, title, deptno) 
empacct_v3 :: [(Attribute,SqlType)]
empacct_v3 =  [ (addEmpacct empno,   TInt32)
              , (addEmpacct name,    TString)
              , (addEmpacct hiredate,TUTCTime)
              , (addEmpacct title,   TString)
              , (addEmpacct deptno,  TInt32)
              ]
  where 
    addEmpacct = flip addRelToAtt empacct

-- | dept (deptname, deptno, managerno)
dept_v345 :: [(Attribute,SqlType)]
dept_v345 =   [ (addDept deptname, TString)
            , (addDept deptno,   TInt32)
            , (managerno,TInt32)
            ]
  where 
    addDept = flip addRelToAtt dept

-- 
-- ** schema version 4 
--

empSchema4 :: Schema 
empSchema4 = (empv4, constructRelMap  [ ( empacct, empacct_v4)
                                                   , ( job, job_v1234)
                                                   , ( dept,  dept_v345)
                                                   , ( empbio,  empbio_v4)
                                                   ]
                    )

-- | empacct (empno, hiredate, title, deptno) 
empacct_v4 :: [(Attribute,SqlType)]
empacct_v4 =   [ (addEmpacct empno,    TInt32)
               , (addEmpacct hiredate, TUTCTime)
               , (addEmpacct title,    TString)
               , (addEmpacct deptno,   TInt32)
               ]
  where 
    addEmpacct = flip addRelToAtt empacct

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: [(Attribute,SqlType)]
empbio_v4 =  [ (addEmpbio empno,    TInt32)
             , (sex,      TString)
             , (birthdate,TUTCTime)
             , (addEmpbio name,     TString)
             ]
  where 
    addEmpbio = flip addRelToAtt empbio
-- 
-- ** schema version 5
-- 

empSchema5 :: Schema 
empSchema5 = ( empv5, constructRelMap [ ( empacct,  empacct_v5)
                                                   , (dept,  dept_v345)
                                                   , (empbio,  empbio_v5)
                                                   ]
             )

-- | empacct (empno, hiredate, title, deptno, salary) 
empacct_v5 :: [(Attribute,SqlType)]
empacct_v5 =   [ (addEmpacct empno,     TInt32)
               , (addEmpacct hiredate,  TUTCTime)
               , (addEmpacct title,     TString)
               , (addEmpacct deptno,    TInt32)
               , (addEmpacct salary,    TInt32)
               ]
  where 
    addEmpacct = flip addRelToAtt empacct

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: [(Attribute,SqlType)]
empbio_v5 =  [ (addEmpbio empno,     TInt32)
             , (sex,      TString)
             , (birthdate, TUTCTime)
             , (firstname, TString)
             , (lastname,  TString)
             ]
  where 
    addEmpbio = flip addRelToAtt empbio



