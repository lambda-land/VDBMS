 -- | An example schema revolution in an employee data base
module VDBMS.UseCases.EmployeeUseCase.EmployeeSchema where


import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
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
genRelation :: Name -> Rename Relation
genRelation name  =  Rename Nothing (Relation name)

engineerpersonnel, otherpersonnel, job, dept, empacct, empbio :: Rename Relation
engineerpersonnel = genRelation "v_engineerpersonnel"
otherpersonnel    = genRelation "v_otherpersonnel"
job               = genRelation "v_job"
dept              = genRelation "v_dept"
empacct           = genRelation "v_empacct"
empbio            = genRelation "v_empbio"


-- 
-- Attributes
-- 
genAttr :: Name -> Rename Attr
genAttr name = Rename Nothing $ Attr (Attribute name) Nothing 

genQualifiedAttr :: Name -> Name -> Rename Attr
genQualifiedAttr rel name = Rename Nothing $ Attr (Attribute name) (Just (RelQualifier (Relation rel)))

empno, name, hiredate, title, deptname, salary :: Rename Attr
deptno, managerno, sex, birthdate, firstname, lastname :: Rename Attr
empno     = genAttr "empno"
name      = genAttr "name"
hiredate  = genAttr "hiredate"
title     = genAttr "title"
deptname  = genAttr "deptname"
salary    = genAttr "salary"
deptno    = genAttr "deptno"
managerno = genAttr"managerno"
sex       = genAttr "sex"
firstname = genAttr "firstname"
lastname  = genAttr "lastname"
birthdate = genAttr "birthdate"


{-
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



-}