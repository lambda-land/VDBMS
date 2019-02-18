 -- | An example schema revolution in an employee data base
module VDB.Example.EmployeeUseCase.EmployeeSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type
import VDB.Variational

import qualified Data.Map as M 
import VDB.Example.SmartConstructor(constructRelMap, constructRowType)

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

engineerpersonnelEmpno, otherpersonnelEmpno, empacctEmpno :: Attribute
empbioEmpno, engineerpersonnelName, otherpersonnelName :: Attribute
empacctName, empbioName, engineerpersonnelHiredate :: Attribute
otherpersonnelHiredate, empacctHiredate, engineerpersonnelTitle :: Attribute
otherpersonnelTitle, empacctTitle, jobTitle, engineerpersonnelDeptname :: Attribute
otherpersonnelDeptname, empacctDeptname, empacctDeptno, deptname :: Attribute
deptno, managerno, jobSalary, empacctSalary, sex, birthdate :: Attribute
firstname, lastname :: Attribute
engineerpersonnelEmpno    = Attribute "engineerpersonnelEmpno"
otherpersonnelEmpno       = Attribute "otherpersonnelEmpno"
empacctEmpno              = Attribute "empacctEmpno"
empbioEmpno               = Attribute "empbioEmpno"
engineerpersonnelName     = Attribute "engineerpersonnelName"
otherpersonnelName        = Attribute "otherpersonnelName"
empacctName               = Attribute "empacctName"
empbioName                = Attribute "empbioName"
engineerpersonnelHiredate = Attribute "engineerpersonnelHiredate"
otherpersonnelHiredate    = Attribute "otherpersonnelHiredate"
empacctHiredate           = Attribute "empacctHiredate"
engineerpersonnelTitle    = Attribute "engineerpersonnelTitle"
otherpersonnelTitle       = Attribute "otherpersonnelTitle"
empacctTitle              = Attribute "empacctTitle"
jobTitle                  = Attribute "jobTitle"
engineerpersonnelDeptname = Attribute "engineerpersonnelDeptname"
otherpersonnelDeptname    = Attribute "otherpersonnelDeptname"
empacctDeptno             = Attribute "empacctDeptno"
empacctDeptname           = Attribute "empacctDeptname"
deptname                  = Attribute "deptname"
deptno                    = Attribute "deptno"
jobSalary                 = Attribute "jobSalary"
empacctSalary             = Attribute "empacctSalary"
managerno                 = Attribute "managerno"
sex                       = Attribute "sex"
firstname                 = Attribute "firstname"
lastname                  = Attribute "lastname"
birthdate                 = Attribute "birthdate"

--  
--  ** schema verison 1 
--  

empSchema1 :: Schema 
empSchema1 = ( Ref (Feature "v1"), constructRelMap [ ( engineerpersonnel,  engineerpersonnel_v1)
                                                   , ( otherpersonnel,    otherpersonnel_v1)
                                                   , ( job,  job_v1)
                                                   ]
             )

-- |  engineerpersonnel(empno, name, hiredate, title, deptname) 
engineerpersonnel_v1 :: [(Attribute,SqlType)]
engineerpersonnel_v1 = [ (engineerpersonnelEmpno, TInt32), 
                         (engineerpersonnelName,  TString)
                       , (engineerpersonnelHiredate, TUTCTime)
                       , (engineerpersonnelTitle,  TString)
                       , (engineerpersonnelDeptname, TString)
                       ]


-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: [(Attribute,SqlType)]
otherpersonnel_v1 =  [ (otherpersonnelEmpno,TInt32)
                     , (otherpersonnelName, TString)
                     , (otherpersonnelHiredate, TUTCTime)
                     , (otherpersonnelTitle, TString)
                     , (otherpersonnelDeptname, TString)
                     ]

-- | job(title, salary)
job_v1 ::[(Attribute,SqlType)]
job_v1 =  [ (jobTitle, TString)
          , (jobSalary,  TInt32)
          ]


-- 
-- ** schema version 2 
-- 

empSchema2 :: Schema 
empSchema2 = (Ref (Feature "v2"), constructRelMap [ (empacct, empacct_v2)
                                                  , (job,  job_v1)
                                                  ] 
              )


-- |  empacct (empno, name, hiredate, title, deptname) 
empacct_v2 :: [(Attribute,SqlType)]
empacct_v2 =  [ ( empacctEmpno,    TInt32)
              , ( empacctName,     TString)
              , ( empacctHiredate, TUTCTime)
              , ( empacctTitle,    TString)
              , ( empacctDeptname, TString)
              ]

-- | job (title, salary)
-- job_v2 :: [(String,SqlType)]
-- job_v2 = [ ( "title", TString)
--          , ( "salary",TInt32) 
--          ]


--
--  ** schema version 3 
-- 

empSchema3 :: Schema
empSchema3 = (Ref (Feature "v3"),  constructRelMap   [ (empacct,  empacct_v3)
                                                     , (job,  job_v1)
                                                     , (dept,  dept_v3)
                                                     ]
              )

-- | empacct (empno, name, hiredate, title, deptno) 
empacct_v3 :: [(Attribute,SqlType)]
empacct_v3 =  [ ( empacctEmpno,   TInt32)
              , ( empacctName,    TString)
              , ( empacctHiredate,TUTCTime)
              , ( empacctTitle,   TString)
              , ( empacctDeptno,  TInt32)
              ]

-- | job (title, salary)
-- job_v3 :: [(String,SqlType)]
-- job_v3 =    [ ( "title",  TString)
--             , ( "salary",  TInt32) 
--             ]

-- | dept (deptname, deptno, managerno)
dept_v3 :: [(Attribute,SqlType)]
dept_v3 =   [ ( deptname, TString)
            , ( deptno,   TInt32)
            , ( managerno,TInt32)
            ]

-- 
-- ** schema version 4 
--

empSchema4 :: Schema 
empSchema4 = (Ref (Feature "v4"), constructRelMap  [ ( empacct, empacct_v4)
                                                   , ( job, job_v1)
                                                   , ( dept,  dept_v3)
                                                   , ( empbio,  empbio_v4)
                                                   ]
                    )

-- | empacct (empno, hiredate, title, deptno) 
empacct_v4 :: [(Attribute,SqlType)]
empacct_v4 =   [ ( empacctEmpno,    TInt32)
               , ( empacctHiredate, TUTCTime)
               , ( empacctTitle,    TString)
               , ( empacctDeptno,   TInt32)
               ]

-- | job (title, salary)
-- job_v4 :: [(String,SqlType)]
-- job_v4 =  [ ( "title",   TString)
--           , ( "salary",  TInt32)
--                           ]

-- | dept (deptname, deptno, managerno) 
-- dept_v4 :: [(String,SqlType)]
-- dept_v4 =   [ ( "deptname",  TString)
--             , ( "deptno",    TInt32)
--             , ( "managerno", TInt32)
--             ]

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: [(Attribute,SqlType)]
empbio_v4 =  [ ( empbioEmpno,    TInt32)
             , ( sex,      TString)
             , ( birthdate,TUTCTime)
             , ( empbioName,     TString)
             ]

-- 
-- ** schema version 5
-- 

empSchema5 :: Schema 
empSchema5 = ( Ref (Feature "v5"), constructRelMap [ ( empacct,  empacct_v5)
                                                   , ( dept,  dept_v3)
                                                   , ( empbio,  empbio_v5)
                                                   ]
             )

-- | empacct (empno, hiredate, title, deptno, salary) 
empacct_v5 :: [(Attribute,SqlType)]
empacct_v5 =   [ ( empacctEmpno,     TInt32)
               , ( empacctHiredate,  TUTCTime)
               , ( empacctTitle,     TString)
               , ( empacctDeptno,    TInt32)
               , ( empacctSalary,    TInt32)
               ]
-- | dept (deptname, deptno, managerno)
-- dept_v5 :: [(String,SqlType)]
-- dept_v5 =  [ ( "deptname",  TString)
--            , ( "deptno",    TInt32)
--            , ( "managerno", TInt32)
--            ]

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: [(Attribute,SqlType)]
empbio_v5 =  [ ( empbioEmpno,     TInt32)
             , ( sex ,      TString)
             , ( birthdate, TUTCTime)
             , ( firstname, TString)
             , ( lastname,  TString)
             ]



