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

empno, name, hiredate, title, deptname, salary :: Attribute
deptno, managerno, sex, birthdate, firstname, lastname :: Attribute
empno     = genAtt "empno"
name      = genAtt "name"
hiredate  = genAtt "hiredate"
title     = genAtt "title"
deptname  = genAtt "deptname"
salary    = Attribute (Just job) "salary"
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
empSchema1 = ( Ref (Feature "v1"), constructRelMap [ ( "v_engineerpersonnel",  engineerpersonnel_v1)
                                                   , ( "v_otherpersonnel",    otherpersonnel_v1)
                                                   , ( "v_job",  job_v1)
                                                   ]
             )

-- |  engineerpersonnel(empno, name, hiredate, title, deptname) 
engineerpersonnel_v1 :: [(String,SqlType)]
engineerpersonnel_v1 = [ ("empno", TInt32), 
                         ("name",  TString)
                       , ("hiredate", TUTCTime)
                       , ("title",  TString)
                       , ("deptname", TString)
                       ]


-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: [(String,SqlType)]
otherpersonnel_v1 =  [ ("empno",TInt32)
                     , ("name", TString)
                     , ("hiredate", TUTCTime)
                     , ("title", TString)
                     , ("deptname", TString)
                     ]

-- | job(title, salary)
job_v1 ::[(String,SqlType)]
job_v1 =  [ ( "title", TString)
          , ("salary",  TInt32)
          ]


-- 
-- ** schema version 2 
-- 

empSchema2 :: Schema 
empSchema2 = (Ref (Feature "v2"), constructRelMap [ ( "v_empacct", empacct_v2)
                                                  , ("v_job",  job_v2)
                                                  ] 
              )


-- |  empacct (empno, name, hiredate, title, deptname) 
empacct_v2 :: [(String,SqlType)]
empacct_v2 =  [ ( "empno",    TInt32)
              , ( "name",     TString)
              , ( "hiredate", TUTCTime)
              , ( "title",    TString)
              , ( "deptname", TString)
              ]

-- | job (title, salary)
job_v2 :: [(String,SqlType)]
job_v2 = [ ( "title", TString)
         , ( "salary",TInt32) 
         ]


--
--  ** schema version 3 
-- 

empSchema3 :: Schema
empSchema3 = (Ref (Feature "v3"),  constructRelMap   [ ("v_empacct",  empacct_v3)
                                                     , ( "v_job",  job_v3)
                                                     , ( "v_dept",  dept_v3)
                                                     ]
              )

-- | empacct (empno, name, hiredate, title, deptno) 
empacct_v3 :: [(String,SqlType)]
empacct_v3 =  [ ( "empno",   TInt32)
              , ( "name",    TString)
              , ( "hiredate",TUTCTime)
              , ( "title",   TString)
              , ( "deptno",  TInt32)
              ]

-- | job (title, salary)
job_v3 :: [(String,SqlType)]
job_v3 =    [ ( "title",  TString)
            , ( "salary",  TInt32) 
            ]

-- | dept (deptname, deptno, managerno)
dept_v3 :: [(String,SqlType)]
dept_v3 =   [ ( "deptname", TString)
            , ( "deptno",   TInt32)
            , ( "managerno",TInt32)
            ]

-- 
-- ** schema version 4 
--

empSchema4 :: Schema 
empSchema4 = (Ref (Feature "v4"), constructRelMap  [ ( "v_empacct", empacct_v4)
                                                   , ( "v_job", job_v4)
                                                   , ( "v_dept",  dept_v4)
                                                   , ( "v_empbio",  empbio_v4)
                                                   ]
                    )

-- | empacct (empno, hiredate, title, deptno) 
empacct_v4 :: [(String,SqlType)]
empacct_v4 =   [ ( "empno",    TInt32)
               , ( "hiredate", TUTCTime)
               , ( "title",    TString)
               , ( "deptno",   TInt32)
               ]

-- | job (title, salary)
job_v4 :: [(String,SqlType)]
job_v4 =  [ ( "title",   TString)
          , ( "salary",  TInt32)
                          ]

-- | dept (deptname, deptno, managerno) 
dept_v4 :: [(String,SqlType)]
dept_v4 =   [ ( "deptname",  TString)
            , ( "deptno",    TInt32)
            , ( "managerno", TInt32)
            ]

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: [(String,SqlType)]
empbio_v4 =  [ ( "empno",    TInt32)
             , ( "sex",      TString)
             , ( "birthdate",TUTCTime)
             , ( "name",     TString)
             ]

-- 
-- ** schema version 5
-- 

empSchema5 :: Schema 
empSchema5 = ( Ref (Feature "v5"), constructRelMap [ ( "v_empacct",  empacct_v5)
                                                   , ( "v_dept",  dept_v5)
                                                   , ( "v_empbio",  empbio_v5)
                                                   ]
             )

-- | empacct (empno, hiredate, title, deptno, salary) 
empacct_v5 :: [(String,SqlType)]
empacct_v5 =   [ ( "empno",     TInt32)
               , ( "hiredate",  TUTCTime)
               , ( "title",     TString)
               , ( "deptno",    TInt32)
               , ( "salary",    TInt32)
               ]
-- | dept (deptname, deptno, managerno)
dept_v5 :: [(String,SqlType)]
dept_v5 =  [ ( "deptname",  TString)
           , ( "deptno",    TInt32)
           , ( "managerno", TInt32)
           ]

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: [(String,SqlType)]
empbio_v5 =  [ ( "empno",     TInt32)
             , ( "sex" ,      TString)
             , ( "birthdate", TUTCTime)
             , ( "firstname", TString)
             , ( "lastname",  TString)
             ]



