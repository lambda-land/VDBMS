 -- | A example schema revolution in an employee data base
module VDB.Example.EmployeeUseCase.EmployeeSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type

import qualified Data.Map as M 

--  
--  ** schema verison 1 
--  

empSchema1 :: Schema 
empSchema1 = ( Ref (Feature "v1"), M.fromList [ (Relation "engineerpersonnel", (Lit True, engineerpersonnel_v1))
                                   , (Relation "otherpersonnel", (Lit True, otherpersonnel_v1))
                                   , (Relation "job", (Lit True, job_v1))
                                   ]
          )

-- |  engineerpersonnel(empno, name, hiredate, title, deptname) 
engineerpersonnel_v1 :: RowType
engineerpersonnel_v1 = M.fromList [ (Attribute "empno",    (Lit True, TInt32))
                                  , (Attribute "name",     (Lit True, TString))
                                  , (Attribute "hiredate", (Lit True, TString))
                                  , (Attribute "title",    (Lit True, TString))
                                  , (Attribute "deptname", (Lit True, TString))
                                  ]

-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: RowType
otherpersonnel_v1 = M.fromList[ (Attribute "empno", (Lit True, TInt32))
                              , (Attribute "name", (Lit True, TString))
                              , (Attribute "hiredate", (Lit True, TString))
                              , (Attribute "title", (Lit True, TString))
                              , (Attribute "deptname", (Lit True, TString))
                              ]

-- | job(title, salary)
job_v1 :: RowType
job_v1 = M.fromList [ (Attribute "title",(Lit True, TString))
                    , (Attribute "salary", (Lit True, TInt32)) 
                    ]


-- 
-- ** schema version 2 
-- 

empSchema2 :: Schema 
empSchema2 = (Ref (Feature "v2"), M.fromList [ (Relation "empacct", (Lit True, empacct_v2))
                                               , (Relation "job", (Lit True, job_v2))
                                                ]
              )


-- |  empacct (empno, name, hiredate, title, deptname) 
empacct_v2 :: RowType
empacct_v2 = M.fromList  [ (Attribute "empno",    (Lit True, TInt32))
                         , (Attribute "name",     (Lit True, TString))
                         , (Attribute "hiredate", (Lit True, TString))
                         , (Attribute "title",    (Lit True, TString))
                         , (Attribute "deptname", (Lit True, TString))
                         ]

-- | job (title, salary)
job_v2 :: RowType
job_v2 = M.fromList[ (Attribute "title", (Lit True, TString))
                   , (Attribute "salary", (Lit True, TInt32)) 
                    ]


--
--  ** schema version 3 
-- 

empSchema3 :: Schema 
empSchema3 = (Ref (Feature "v3"), M.fromList [ (Relation "empacct", (Lit True, empacct_v3))
                                   , (Relation "job", (Lit True, job_v3))
                                   , (Relation "dept", (Lit True, dept_v3))
                                   ]
              )

-- | empacct (empno, name, hiredate, title, deptno) 
empacct_v3 :: RowType
empacct_v3 = M.fromList [ (Attribute "empno",    (Lit True, TInt32))
                        , (Attribute "name",     (Lit True, TString))
                        , (Attribute "hiredate", (Lit True, TString))
                        , (Attribute "title",    (Lit True, TString))
                        , (Attribute "deptno",   (Lit True, TInt32))
                        ]

-- | job (title, salary)
job_v3 :: RowType
job_v3 =  M.fromList[ (Attribute "title",  (Lit True, TString))
                    , (Attribute "salary", (Lit True, TInt32)) 
                    ]

-- | dept (deptname, deptno, managerno)
dept_v3 :: RowType
dept_v3 = M.fromList[ (Attribute "deptname",  (Lit True, TString))
                    , (Attribute "deptno",    (Lit True, TInt32))
                    , (Attribute "managerno", (Lit True, TInt32))
                    ]

-- 
-- ** schema version 4 
--

empSchema4 :: Schema 
empSchema4 = (Ref (Feature "v4"), M.fromList [ (Relation "empacct", (Lit True, empacct_v4))
                                             , (Relation "job", (Lit True, job_v4))
                                             , (Relation "dept", (Lit True, dept_v4))
                                             , (Relation "empbio", (Lit True, empbio_v4))
                                             ]
                    )

-- | empacct (empno, hiredate, title, deptno) 
empacct_v4 :: RowType
empacct_v4 =  M.fromList [ (Attribute "empno",    (Lit True, TInt32))
                         , (Attribute "hiredate", (Lit True, TString))
                         , (Attribute "title",    (Lit True, TString))
                         , (Attribute "deptno",   (Lit True, TInt32))
                         ]

-- | job (title, salary)
job_v4 :: RowType
job_v4 = M.fromList [ (Attribute "title",  (Lit True, TString))
                    , (Attribute "salary", (Lit True, TInt32)) 
                    ]

-- | dept (deptname, deptno, managerno) 
dept_v4 :: RowType
dept_v4 = M.fromList  [ (Attribute "deptname", (Lit True, TString))
                      , (Attribute "deptno", (Lit True, TInt32))
                      , (Attribute "managerno", (Lit True, TInt32))
                      ]

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: RowType
empbio_v4 = M.fromList [ (Attribute "empno", (Lit True, TInt32))
                       , (Attribute "sex", (Lit True, TString))
                       , (Attribute "birthdate", (Lit True, TString))
                       , (Attribute "name", (Lit True, TString))
                       ]

-- 
-- ** schema version 5
-- 

empSchema5 :: Schema 
empSchema5 = (Ref (Feature "v5"), M.fromList [ (Relation "empacct", (Lit True, empacct_v5))
                                   , (Relation "dept", (Lit True, dept_v5))
                                   , (Relation "empbio", (Lit True, empbio_v5))
                                   ]
          )

-- | empacct (empno, hiredate, title, deptno, salary) 
empacct_v5 :: RowType
empacct_v5 = M.fromList[ (Attribute "empno",    (Lit True, TInt32))
                       , (Attribute "hiredate", (Lit True, TString))
                       , (Attribute "title",    (Lit True, TString))
                       , (Attribute "deptno",   (Lit True, TInt32))
                       , (Attribute "salary",   (Lit True, TInt32))
                       ]
-- | dept (deptname, deptno, managerno)
dept_v5 :: RowType
dept_v5 = M.fromList[ (Attribute "deptname", (Lit True, TString))
                    , (Attribute "deptno", (Lit True, TInt32))
                    , (Attribute "managerno", (Lit True, TInt32))
                    ]

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: RowType
empbio_v5 = M.fromList[ (Attribute "empno",     (Lit True, TInt32))
                      , (Attribute "sex" ,      (Lit True, TString))
                      , (Attribute "birthdate", (Lit True, TString))
                      , (Attribute "firstname", (Lit True, TString))
                      , (Attribute "lastname",  (Lit True, TString))
                      ]




