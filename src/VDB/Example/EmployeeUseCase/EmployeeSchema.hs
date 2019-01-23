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

-- | contruct plain Schema without tag assigned based on a list of [(Relatin Name, [Attribute name, Sqltype])] 
constructRelMap :: [(String, [(String, SqlType)])] -> M.Map Relation (Opt RowType) 
constructRelMap nrlist = M.fromList $ map (\(relName, rt) -> ( Relation relName, (Lit True, constructRowType relName rt))) nrlist

-- | contruct rowType based on a list of [(Attribute Name, SqlType)]
constructRowType ::  String -> [(String,SqlType)]  -> RowType
constructRowType relName attrTypeList  = M.fromList  $ map (\(attrName, t) -> ( Attribute (Just (Relation relName)) attrName, (Lit True, t))) attrTypeList

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
empSchema2 = (Ref (Feature "v2"), constructRelMap [ ( "empacct", empacct_v2)
                                                  , ("job",  job_v2)
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
empSchema3 = (Ref (Feature "v3"),  constructRelMap   [ ("empacct",  empacct_v3)
                                                     , ( "job",  job_v3)
                                                     , ( "dept",  dept_v3)
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
empSchema4 = (Ref (Feature "v4"), constructRelMap  [ ( "empacct", empacct_v4)
                                                   , ( "job", job_v4)
                                                   , ( "dept",  dept_v4)
                                                   , ( "empbio",  empbio_v4)
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
empSchema5 = ( Ref (Feature "v5"), constructRelMap [ ( "empacct",  empacct_v5)
                                                   , ( "dept",  dept_v5)
                                                   , ( "empbio",  empbio_v5)
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



