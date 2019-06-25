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
empno     = Attribute "empno"
name      = Attribute "name"
hiredate  = Attribute "hiredate"
title     = Attribute "title"
deptname  = Attribute "deptname"
salary    = Attribute "salary"
deptno    = Attribute "deptno"
managerno = Attribute "managerno"
sex       = Attribute "sex"
firstname = Attribute "firstname"
lastname  = Attribute "lastname"
birthdate = Attribute "birthdate"

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
engineerpersonnel_v1 = [ ( empno, TInt32), 
                         ( name,  TString)
                       , ( hiredate, TUTCTime)
                       , ( title,  TString)
                       , ( deptname, TString)
                       ]

-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: [(Attribute,SqlType)]
otherpersonnel_v1 =  [ ( empno,TInt32)
                     , ( name, TString)
                     , ( hiredate, TUTCTime)
                     , ( title, TString)
                     , ( deptname, TString)
                     ]

-- | job(title, salary)
job_v1234 ::[(Attribute,SqlType)]
job_v1234 = [ (title, TString)
            , (salary,  TInt32)
          ]

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
empacct_v2 =  [ ( empno,    TInt32)
              , ( name,     TString)
              , ( hiredate, TUTCTime)
              , ( title,    TString)
              , ( deptname, TString)
              ]

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
empacct_v3 =  [ ( empno,   TInt32)
              , ( name,    TString)
              , ( hiredate,TUTCTime)
              , ( title,   TString)
              , ( deptno,  TInt32)
              ]

-- | dept (deptname, deptno, managerno)
dept_v345 :: [(Attribute,SqlType)]
dept_v345 =   [ (deptname, TString)
            , (deptno,   TInt32)
            , (managerno,TInt32)
            ]

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
empacct_v4 =   [ ( empno,    TInt32)
               , ( hiredate, TUTCTime)
               , ( title,    TString)
               , ( deptno,   TInt32)
               ]

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: [(Attribute,SqlType)]
empbio_v4 =  [ ( empno,    TInt32)
             , (sex,      TString)
             , (birthdate,TUTCTime)
             , ( name,     TString)
             ]
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
empacct_v5 =   [ ( empno,     TInt32)
               , ( hiredate,  TUTCTime)
               , ( title,     TString)
               , ( deptno,    TInt32)
               , ( salary,    TInt32)
               ]

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: [(Attribute,SqlType)]
empbio_v5 =  [ ( empno,     TInt32)
             , (sex,      TString)
             , (birthdate, TUTCTime)
             , (firstname, TString)
             , (lastname,  TString)
             ]


