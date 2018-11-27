 -- | A example schema revolution in an employee data base
module VDB.Example.EmployeeUseCase.EmployeeSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Value 

import qualified Data.Map as Map 

--  
--  ** schema verison 1 
--  

schema1 :: Schema 
schema1 = ( Ref "v1", Map.fromList [ (Relation "engineerpersonnel", (Lit True, engineerpersonnel_v1))
                                   , (Relation "otherpersonnel", (Lit True, otherpersonnel_v1))
                                   , (Relation "job", (Lit True, job_v1))
                                   ]
          )

-- |  engineerpersonnel(empno, name, hiredate, title, deptname) 
engineerpersonnel_v1 :: RowType
engineerpersonnel_v1 = [ (Lit True, (Attribute "empno", TInt))
                    , (Lit True, (Attribute "name", TString))
                    , (Lit True, (Attribute "hiredate", TString))
                    , (Lit True, (Attribute "title", TString))
                    , (Lit True, (Attribute "deptname", TString))
                    ]

-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: RowType
otherpersonnel_v1 = [ (Lit True, (Attribute "empno", TInt))
                 , (Lit True, (Attribute "name", TString))
                 , (Lit True, (Attribute "hiredate", TString))
                 , (Lit True, (Attribute "title", TString))
                 , (Lit True, (Attribute "deptname", TString))
                 ]

-- | job(title, salary)
job_v1 :: RowType
job_v1 = [ (Lit True, (Attribute "title", TString))
      , (Lit True, (Attribute "salary", TInt)) 
      ]


-- 
-- ** schema version 2 
-- 

schema2 :: Schema 
schema2 = ( Ref "v2", Map.fromList [ (Relation "empacct", (Lit True, empacct_v2))
                                   , (Relation "job", (Lit True, job_v2))
                                   ]
          )


-- |  empacct (empno, name, hiredate, title, deptname) 
empacct_v2 :: RowType
empacct_v2 = [ (Lit True, (Attribute "empno", TInt))
             , (Lit True, (Attribute "name", TString))
             , (Lit True, (Attribute "hiredate", TString))
             , (Lit True, (Attribute "title", TString))
             , (Lit True, (Attribute "deptname", TString))
             ]

-- | job (title, salary)
job_v2 :: RowType
job_v2 = [ (Lit True, (Attribute "title", TString))
         , (Lit True, (Attribute "salary", TInt)) 
         ]


--
--  ** schema version 3 
-- 

schema3 :: Schema 
schema3 = ( Ref "v3", Map.fromList [ (Relation "empacct", (Lit True, empacct_v3))
                                   , (Relation "job", (Lit True, job_v3))
                                   , (Relation "dept", (Lit True, dept_v3))
                                   ]
          )

-- | empacct (empno, name, hiredate, title, deptno) 
empacct_v3 :: RowType
empacct_v3 = [ (Lit True, (Attribute "empno", TInt))
             , (Lit True, (Attribute "name", TString))
             , (Lit True, (Attribute "hiredate", TString))
             , (Lit True, (Attribute "title", TString))
             , (Lit True, (Attribute "deptno", TInt))
             ]

-- | job (title, salary)
job_v3 :: RowType
job_v3 = [ (Lit True, (Attribute "title", TString))
         , (Lit True, (Attribute "salary", TInt)) 
         ]

-- | dept (deptname, deptno, managerno)
dept_v3 :: RowType
dept_v3 = [ (Lit True, (Attribute "deptname", TString))
          , (Lit True, (Attribute "deptno", TInt))
          , (Lit True, (Attribute "managerno", TInt))
          ]

-- 
-- ** schema version 4 
--

schema4 :: Schema 
schema4 = ( Ref "v4", Map.fromList [ (Relation "empacct", (Lit True, empacct_v4))
                                   , (Relation "job", (Lit True, job_v4))
                                   , (Relation "dept", (Lit True, dept_v4))
                                   , (Relation "empbio", (Lit True, empbio_v4))
                                   ]
          )

-- | empacct (empno, hiredate, title, deptno) 
empacct_v4 :: RowType
empacct_v4 = [ (Lit True, (Attribute "empno", TInt))
             , (Lit True, (Attribute "hiredate", TString))
             , (Lit True, (Attribute "title", TString))
             , (Lit True, (Attribute "deptno", TInt))
             ]
-- | job (title, salary)
job_v4 :: RowType
job_v4 = [ (Lit True, (Attribute "title", TString))
         , (Lit True, (Attribute "salary", TInt)) 
         ]

-- | dept (deptname, deptno, managerno) 
dept_v4 :: RowType
dept_v4 = [ (Lit True, (Attribute "deptname", TString))
          , (Lit True, (Attribute "deptno", TInt))
          , (Lit True, (Attribute "managerno", TInt))
          ]

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: RowType
empbio_v4 = [ (Lit True, (Attribute "empno", TInt))
         , (Lit True, (Attribute "sex", TString))
         , (Lit True, (Attribute "birthdate", TString))
         , (Lit True, (Attribute "name", TString))
         ]

-- 
-- ** schema version 5
-- 

schema5 :: Schema 
schema5 = ( Ref "v5", Map.fromList [ (Relation "empacct", (Lit True, empacct_v5))
                                   , (Relation "dept", (Lit True, dept_v5))
                                   , (Relation "empbio", (Lit True, empbio_v5))
                                   ]
          )

-- | empacct (empno, hiredate, title, deptno, salary) 
empacct_v5 :: RowType
empacct_v5 = [ (Lit True, (Attribute "empno", TInt))
             , (Lit True, (Attribute "hiredate", TString))
             , (Lit True, (Attribute "title", TString))
             , (Lit True, (Attribute "deptno", TInt))
             , (Lit True, (Attribute "salary", TInt))
             ]
-- | dept (deptname, deptno, managerno)
dept_v5 :: RowType
dept_v5 = [ (Lit True, (Attribute "deptname", TString))
          , (Lit True, (Attribute "deptno", TInt))
          , (Lit True, (Attribute "managerno", TInt))
          ]

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: RowType
empbio_v5 = [ (Lit True, (Attribute "empno", TInt))
            , (Lit True, (Attribute "sex", TString))
            , (Lit True, (Attribute "birthdate", TString))
            , (Lit True, (Attribute "firstname", TString))
            , (Lit True, (Attribute "lastname", TString))
            ]





