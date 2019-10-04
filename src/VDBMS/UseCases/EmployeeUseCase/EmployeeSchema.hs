 -- | An example schema revolution in an employee data base
module VDBMS.UseCases.EmployeeUseCase.EmployeeSchema where


import VDBMS.Features.FeatureExpr.FeatureExpr
import qualified VDBMS.VDB.Name as N 
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Value.Value
import VDBMS.UseCases.SmartConstructor



-- 
-- Features
-- 
empv1, empv2, empv3, empv4, empv5 :: FeatureExpr
empv1 = Ref (Feature "v1")
empv2 = Ref (Feature "v2")
empv3 = Ref (Feature "v3")
empv4 = Ref (Feature "v4")
empv5 = Ref (Feature "v5")


-- 
-- Relations
-- 
engineerpersonnel, otherpersonnel, job, dept, empacct, empbio :: N.Relation
engineerpersonnel = N.Relation "v_engineerpersonnel"
otherpersonnel    = N.Relation "v_otherpersonnel"
job               = N.Relation "v_job"
dept              = N.Relation "v_dept"
empacct           = N.Relation "v_empacct"
empbio            = N.Relation "v_empbio"

-- 
-- Attributes
-- 
empno, name, hiredate, title, deptname, salary :: N.Attr
deptno, managerno, sex, birthdate, firstname, lastname :: N.Attr
empno     = attr "empno"
name      = attr "name"
hiredate  = attr "hiredate"
title     = attr "title"
deptname  = attr "deptname"
salary    = attr "salary"
deptno    = attr "deptno"
managerno = attr"managerno"
sex       = attr "sex"
firstname = attr "firstname"
lastname  = attr "lastname"
birthdate = attr "birthdate"

empno_, name_, hiredate_, title_, deptname_, salary_ :: N.Attribute
deptno_, managerno_, sex_, birthdate_, firstname_, lastname_ :: N.Attribute
empno_     = N.Attribute "empno"
name_      = N.Attribute "name"
hiredate_  = N.Attribute "hiredate"
title_     = N.Attribute "title"
deptname_  = N.Attribute "deptname"
salary_    = N.Attribute "salary"
deptno_    = N.Attribute "deptno"
managerno_ = N.Attribute "managerno"
sex_       = N.Attribute "sex"
firstname_ = N.Attribute "firstname"
lastname_  = N.Attribute "lastname"
birthdate_ = N.Attribute "birthdate"

--  
--  ** schema for verison 1 
--  

empSchema1 :: Schema 
empSchema1 = ( empv1, constructRelMap [ ( engineerpersonnel,  engineerpersonnel_v1)
                                                   , ( otherpersonnel,    otherpersonnel_v1)
                                                   , ( job,  job_v1234)
                                                   ]
             )

-- |  engineerpersonnel(empno, name, hiredate, title, deptname) 
engineerpersonnel_v1 :: [(N.Attribute,SqlType)]
engineerpersonnel_v1 = [ (empno_, TInt32), 
                         (name_,  TString)
                       , (hiredate_, TUTCTime)
                       , (title_,  TString)
                       , (deptname_, TString)
                       ]

-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: [(N.Attribute,SqlType)]
otherpersonnel_v1 =  [ (empno_,TInt32)
                     , (name_, TString)
                     , (hiredate_, TUTCTime)
                     , (title_, TString)
                     , (deptname_, TString)
                     ]

-- | job(title, salary)
job_v1234 ::[(N.Attribute,SqlType)]
job_v1234 = [ (title_, TString)
            , (salary_,  TInt32)
            ]

{-
-- 
-- ** schema version 2 
-- 

empSchema2 :: Schema 
empSchema2 = (empv2, constructRelMap [ ( empacct, empacct_v2)
                                                  , (job,  job_v1234)
                                                  ] 
              )


-- |  empacct (empno, name, hiredate, title, deptname) 
empacct_v2 :: [(N.Attribute,SqlType)]
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
empacct_v3 :: [(N.Attribute,SqlType)]
empacct_v3 =  [ (addEmpacct empno,   TInt32)
              , (addEmpacct name,    TString)
              , (addEmpacct hiredate,TUTCTime)
              , (addEmpacct title,   TString)
              , (addEmpacct deptno,  TInt32)
              ]
  where 
    addEmpacct = flip addRelToAtt empacct

-- | dept (deptname, deptno, managerno)
dept_v345 :: [(N.Attribute,SqlType)]
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
empacct_v4 :: [(N.Attribute,SqlType)]
empacct_v4 =   [ (addEmpacct empno,    TInt32)
               , (addEmpacct hiredate, TUTCTime)
               , (addEmpacct title,    TString)
               , (addEmpacct deptno,   TInt32)
               ]
  where 
    addEmpacct = flip addRelToAtt empacct

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: [(N.Attribute,SqlType)]
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
empacct_v5 :: [(N.Attribute,SqlType)]
empacct_v5 =   [ (addEmpacct empno,     TInt32)
               , (addEmpacct hiredate,  TUTCTime)
               , (addEmpacct title,     TString)
               , (addEmpacct deptno,    TInt32)
               , (addEmpacct salary,    TInt32)
               ]
  where 
    addEmpacct = flip addRelToAtt empacct

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: [(N.Attribute,SqlType)]
empbio_v5 =  [ (addEmpbio empno,     TInt32)
             , (sex,      TString)
             , (birthdate, TUTCTime)
             , (firstname, TString)
             , (lastname,  TString)
             ]
  where 
    addEmpbio = flip addRelToAtt empbio



-}