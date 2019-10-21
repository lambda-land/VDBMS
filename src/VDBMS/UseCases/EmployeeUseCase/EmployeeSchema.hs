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
-- Employee v-schema 
--

employeeFeatureModel :: FeatureExpr
employeeFeatureModel =  (empv1 `And` (Not empv2) `And` (Not empv3) `And` (Not empv4) `And` (Not empv5)) `Or` 
                        ((Not empv1) `And` empv2 `And` (Not empv3) `And` (Not empv4) `And` (Not empv5)) `Or` 
                        ((Not empv1) `And` (Not empv2) `And` empv3`And` (Not empv4) `And` (Not empv5)) `Or` 
                        ((Not empv1) `And` (Not empv2) `And` (Not empv3) `And` empv4 `And` (Not empv5)) `Or` 
                        ((Not empv1) `And` (Not empv2) `And` (Not empv3) `And` (Not empv4) `And` empv5)  

empVSchema :: Schema 
empVSchema = (employeeFeatureModel, constructOptRelMap [ (empv1, engineerpersonnel, engineerpersonnel_vschema)
                                                       , (empv1, otherpersonnel, otherpersonnel_vschema)
                                                       , (empv2 `And` empv3 `And` empv4 `And` empv5, empacct, empacct_vschema)
                                                       , (empv1 `And` empv2 `And` empv3 `And` empv4, job, job_vschema)
                                                       , (empv3 `And` empv4 `And` empv5, dept, dept_vschema)
                                                       , (empv4 `And` empv5, empbio, empbio_vschema)])

engineerpersonnel_vschema, otherpersonnel_vschema, empacct_vschema, job_vschema, dept_vschema, empbio_vschema :: [(FeatureExpr, N.Attribute, SqlType)] 
engineerpersonnel_vschema =  [ (Lit True, empno_, TInt32)
                             , (Lit True, name_,  TString)
                             , (Lit True, hiredate_, TUTCTime)
                             , (Lit True, title_,  TString)
                             , (Lit True, deptname_, TString)
                             ] 
otherpersonnel_vschema = [ (Lit True, empno_, TInt32)
                         , (Lit True, name_,  TString)
                         , (Lit True, hiredate_, TUTCTime)
                         , (Lit True, title_,  TString)
                         , (Lit True, deptname_, TString)
                         ] 
empacct_vschema = [ (Lit True, empno_,    TInt32)
                  , (empv2 `Or` empv3, name_,     TString)
                  , (Lit True, hiredate_, TUTCTime)
                  , (Lit True, title_,    TString)
                  , (empv2, deptname_, TString)
                  , (empv3 `Or` empv4 `Or` empv5, deptno_,  TInt32)
                  , (empv5, salary_,    TInt32)
                  ] 
job_vschema = [ (Lit True, title_, TString)
              , (Lit True, salary_,  TInt32)
              ] 
dept_vschema = [ (Lit True, deptname_, TString)
               , (Lit True, deptno_,   TInt32)
               , (Lit True, managerno_,TInt32)
               ]
 
empbio_vschema=  [ (Lit True, empno_,     TInt32)
                 , (Lit True, sex_,      TString)
                 , (Lit True, birthdate_, TUTCTime)
                 , (empv4, name_,     TString)
                 , (empv5, firstname_, TString)
                 , (empv5, lastname_,  TString)
                 ] 

--
--  ** schema for verison 1 
--  
empSchema1 :: Schema 
empSchema1 = ( empv1, constructRelMap [ ( engineerpersonnel,  engineerpersonnel_v1)
                                      , ( otherpersonnel,    otherpersonnel_v1)
                                      , ( job,  job_v1234)
                                      ]
             )

-- |  engineerpersonnel(empno_, name_, hiredate_, title_, deptname_) 
engineerpersonnel_v1 :: [(N.Attribute, SqlType)]
engineerpersonnel_v1 = [ (empno_, TInt32), 
                         (name_,  TString)
                       , (hiredate_, TUTCTime)
                       , (title_,  TString)
                       , (deptname_, TString)
                       ]

-- | otherpersonnel(empno_, name_, hiredate_, title_, deptname_) 
otherpersonnel_v1 :: [(N.Attribute,SqlType)]
otherpersonnel_v1 =  [ (empno_,TInt32)
                     , (name_, TString)
                     , (hiredate_, TUTCTime)
                     , (title_, TString)
                     , (deptname_, TString)
                     ]

-- | job(title_, salary_)
job_v1234 ::[(N.Attribute,SqlType)]
job_v1234 = [ (title_, TString)
            , (salary_,  TInt32)
            ]

-- 
-- ** schema version 2 
-- 

empSchema2 :: Schema 
empSchema2 = (empv2, constructRelMap [ ( empacct, empacct_v2)
                                     , (job,  job_v1234)
                                     ] 
              )


-- |  empacct (empno_, name_, hiredate_, title_, deptname_) 
empacct_v2 :: [(N.Attribute,SqlType)]
empacct_v2 =  [ (empno_,    TInt32)
              , (name_,     TString)
              , (hiredate_, TUTCTime)
              , (title_,    TString)
              , (deptname_, TString)
              ]

--
--  ** schema version 3 
-- 
empSchema3 :: Schema
empSchema3 = (empv3,  constructRelMap  [ (empacct,  empacct_v3)
                                       , ( job,  job_v1234)
                                       , ( dept,  dept_v345)
                                       ]
              )

-- | empacct (empno_, name_, hiredate_, title_, deptno_) 
empacct_v3 :: [(N.Attribute,SqlType)]
empacct_v3 =  [ (empno_,   TInt32)
              , (name_,    TString)
              , (hiredate_,TUTCTime)
              , (title_,   TString)
              , (deptno_,  TInt32)
              ]

-- | dept (deptname_, deptno_, managerno_)
dept_v345 :: [(N.Attribute,SqlType)]
dept_v345 =   [ (deptname_, TString)
              , (deptno_,   TInt32)
              , (managerno_,TInt32)
              ]

-- 
-- ** schema version 4 
--
empSchema4 :: Schema 
empSchema4 = (empv4, constructRelMap [ ( empacct, empacct_v4)
                                     , ( job, job_v1234)
                                     , ( dept,  dept_v345)
                                     , ( empbio,  empbio_v4)
                                     ]
                    )

-- | empacct (empno_, hiredate_, title_, deptno_) 
empacct_v4 :: [(N.Attribute,SqlType)]
empacct_v4 =   [ (empno_,    TInt32)
               , (hiredate_, TUTCTime)
               , (title_,    TString)
               , (deptno_,   TInt32)
               ]

-- | empbio (empno_, sex_, birthdate_, name_)
empbio_v4 :: [(N.Attribute,SqlType)]
empbio_v4 =  [ (empno_,    TInt32)
             , (sex_,      TString)
             , (birthdate_,TUTCTime)
             , (name_,     TString)
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

-- | empacct (empno_, hiredate_, title_, deptno_, salary_) 
empacct_v5 :: [(N.Attribute,SqlType)]
empacct_v5 =   [ (empno_,     TInt32)
               , (hiredate_,  TUTCTime)
               , (title_,     TString)
               , (deptno_,    TInt32)
               , (salary_,    TInt32)
               ]

-- | empbio (empno_, sex_, birthdate_, firstname_, lastname_)
empbio_v5 :: [(N.Attribute,SqlType)]
empbio_v5 =  [ (empno_,     TInt32)
             , (sex_,      TString)
             , (birthdate_, TUTCTime)
             , (firstname_, TString)
             , (lastname_,  TString)
             ]