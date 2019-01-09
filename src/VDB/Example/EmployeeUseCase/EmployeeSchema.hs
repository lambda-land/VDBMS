 -- | An example schema revolution in an employee data base
module VDB.Example.EmployeeUseCase.EmployeeSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type
import VDB.Variational

import qualified Data.Map as M 

--
-- smart contructor for building schema 
--

-- | contruct rowType based on a list of [(Attribute Name, SqlType)]
constructRowType :: [(String,SqlType)] -> RowType
constructRowType attrTypeList = M.fromList  $ map (\(attrName, t) -> ( Attribute Nothing attrName, (Lit True, t))) attrTypeList

-- | contruct plain Schema without tag assigned based on a list of [(Relatin Name, Rowtype)] 
constructRelMap :: [(String, RowType)] -> M.Map Relation (Opt RowType) 
constructRelMap nrlist = M.fromList $ map (\(relName, rt) -> ( Relation relName, (Lit True, rt))) nrlist


--  
--  ** schema verison 1 
--  

empSchema1 :: Schema 
empSchema1 = ( Ref (Feature "v1"), constructRelMap [ ( "engineerpersonnel",  engineerpersonnel_v1)
                                                   , ( "otherpersonnel",    otherpersonnel_v1)
                                                   , ( "job",  job_v1)
                                                   ]
             )

-- |  engineerpersonnel(empno, name, hiredate, title, deptname) 
engineerpersonnel_v1 :: RowType
engineerpersonnel_v1 = constructRowType [ ("empno", TInt32)
                                        , ("name",  TString)
                                        , ("hiredate", TString)
                                        , ("title",  TString)
                                        , ("deptname", TString)
                                        ]


-- | otherpersonnel(empno, name, hiredate, title, deptname) 
otherpersonnel_v1 :: RowType
otherpersonnel_v1 = constructRowType [ ("empno",TInt32)
                                     , ("name", TString)
                                     , ("hiredate", TString)
                                     , ("title", TString)
                                     , ("deptname", TString)
                                     ]

-- | job(title, salary)
job_v1 :: RowType
job_v1 = constructRowType [ ( "title", TString)
                          , ("salary",  TInt32)
                          ]


-- 
-- ** schema version 2 
-- 

empSchema2 :: Schema 
empSchema2 = (Ref (Feature "v2"), constructRelMap [ ( "empacct", empacct_v2)
                                                  , ("job",  job_v2)
                                                  ] 
              )


-- |  empacct (empno, name, hiredate, title, deptname) 
empacct_v2 :: RowType
empacct_v2 = constructRowType [ ( "empno",    TInt32)
                              , ( "name",     TString)
                              , ( "hiredate", TString)
                              , ( "title",    TString)
                              , ( "deptname", TString)
                              ]

-- | job (title, salary)
job_v2 :: RowType
job_v2 = constructRowType[ ( "title", TString)
                         , ( "salary",TInt32) 
                         ]


--
--  ** schema version 3 
-- 

empSchema3 :: Schema 
empSchema3 = (Ref (Feature "v3"), constructRelMap  [ ("empacct",  empacct_v3)
                                                   , ( "job",  job_v3)
                                                   , ( "dept",  dept_v3)
                                                   ]
              )

-- | empacct (empno, name, hiredate, title, deptno) 
empacct_v3 :: RowType
empacct_v3 =constructRowType  [ ( "empno",   TInt32)
                              , ( "name",    TString)
                              , ( "hiredate",TString)
                              , ( "title",   TString)
                              , ( "deptno",  TInt32)
                              ]

-- | job (title, salary)
job_v3 :: RowType
job_v3 =  constructRowType  [ ( "title",  TString)
                            , ( "salary",  TInt32) 
                            ]

-- | dept (deptname, deptno, managerno)
dept_v3 :: RowType
dept_v3 = constructRowType  [ ( "deptname", TString)
                            , ( "deptno",   TInt32)
                            , ( "managerno",TInt32)
                            ]

-- 
-- ** schema version 4 
--

empSchema4 :: Schema 
empSchema4 = (Ref (Feature "v4"), constructRelMap  [ ( "empacct", empacct_v4)
                                                   , ( "job", job_v4)
                                                   , ( "dept",  dept_v4)
                                                   , ( "empbio",  empbio_v4)
                                                   ]
                    )

-- | empacct (empno, hiredate, title, deptno) 
empacct_v4 :: RowType
empacct_v4 =  constructRowType [ ( "empno",    TInt32)
                               , ( "hiredate", TString)
                               , ( "title",    TString)
                               , ( "deptno",   TInt32)
                               ]

-- | job (title, salary)
job_v4 :: RowType
job_v4 = constructRowType [ ( "title",   TString)
                          , ( "salary",  TInt32)
                          ]

-- | dept (deptname, deptno, managerno) 
dept_v4 :: RowType
dept_v4 = constructRowType  [ ( "deptname",  TString)
                            , ( "deptno",    TInt32)
                            , ( "managerno", TInt32)
                            ]

-- | empbio (empno, sex, birthdate, name)
empbio_v4 :: RowType
empbio_v4 =constructRowType  [ ( "empno",    TInt32)
                             , ( "sex",      TString)
                             , ( "birthdate",TString)
                             , ( "name",     TString)
                             ]

-- 
-- ** schema version 5
-- 

empSchema5 :: Schema 
empSchema5 = ( Ref (Feature "v5"), constructRelMap [ ( "empacct",  empacct_v5)
                                                   , ( "dept",  dept_v5)
                                                   , ( "empbio",  empbio_v5)
                                                   ]
             )

-- | empacct (empno, hiredate, title, deptno, salary) 
empacct_v5 :: RowType
empacct_v5 = constructRowType  [ ( "empno",     TInt32)
                               , ( "hiredate",  TString)
                               , ( "title",     TString)
                               , ( "deptno",    TInt32)
                               , ( "salary",    TInt32)
                               ]
-- | dept (deptname, deptno, managerno)
dept_v5 :: RowType
dept_v5 = constructRowType [ ( "deptname",  TString)
                           , ( "deptno",    TInt32)
                           , ( "managerno", TInt32)
                           ]

-- | empbio (empno, sex, birthdate, firstname, lastname)
empbio_v5 :: RowType
empbio_v5 = constructRowType [ ( "empno",     TInt32)
                             , ( "sex" ,      TString)
                             , ( "birthdate", TString)
                             , ( "firstname", TString)
                             , ( "lastname",  TString)
                             ]




