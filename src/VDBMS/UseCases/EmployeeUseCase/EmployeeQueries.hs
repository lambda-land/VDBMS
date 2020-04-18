-- | vqs for employee database.
module VDBMS.UseCases.EmployeeUseCase.EmployeeQueries where

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.UseCases.EmployeeUseCase.EmployeeSchema
import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import qualified VDBMS.QueryLang.RelAlg.Variational.Condition as C
import VDBMS.QueryLang.RelAlg.Variational.SmartConstructor
import VDBMS.DBMS.Value.CompOp
import Prelude hiding (Ordering(..))
import Database.HDBC 
import VDBMS.VDB.Name hiding (name)
-- import VDBMS.VDB.GenName

-- import Data.Time.LocalTime
import Data.Time.Calendar

-- need to run the following
-- numVarintQ empVQ8 empConfs
-- numUniqueVariantQ empVQ8

--
-- * Constant values used for employee use cases
--

-- | the year 1991 condition
--   ModifiedJulianDay Int (Count days from 1858-11-17)
--   1991-01-01: ModifiedJulianDay 48257
--   1992-01-01: ModifiedJulianDay 48622
date19910101, date19920101 :: Day
date19910101 = ModifiedJulianDay 48257
date19920101 = ModifiedJulianDay 48622

-- | 1991-01-01 < hiredate < 1992-01-0
yearCond :: C.Condition 
yearCond = C.And (C.Comp GT (C.Val $ SqlLocalDate date19910101) (C.Att  hiredate))
                 (C.Comp LT (C.Att hiredate) (C.Val $ SqlLocalDate date19920101))

-- |  hiredate > 1991-01-01
yearAfterCond :: C.Condition 
yearAfterCond = C.Comp GT (C.Att hiredate) (C.Val $ SqlLocalDate date19910101) 

-- | employee id = 10004 condition
empCond :: C.Condition
empCond = C.Comp EQ (C.Att empno) (C.Val empno_value)

empSqlCond :: VsqlCond
empSqlCond = VsqlCond empCond

empno_value :: SqlValue 
empno_value  = SqlInt32 10004

departno_value :: SqlValue
departno_value = SqlString "d001"

temp :: Name
temp = "temp"

v345 :: F.FeatureExpr
v345 = F.Or v34 empv5

v34 :: F.FeatureExpr
v34 = F.Or empv3 empv4

v45 :: F.FeatureExpr
v45 = F.Or empv4 empv5

-- empFromEmpacct :: Rename Algebra
-- empFromEmpacct = genSubquery "emp" $ Sel (VsqlCond empCond) (renameNothing (tRef empacct))

-- empFromEmpacctUnnamed :: Rename Algebra
-- empFromEmpacctUnnamed = genRenameAlgebra $ Sel (VsqlCond empCond) (renameNothing (tRef empacct))

--
-- * Queries based on Prima paper
-- Intents are taken from the prima paper, adjusted to the employee database. 
-- 1. We have year 1991, instead of year 2003. 
-- 2. We use features to identify the variants, instead of timestamps.

-- 1(Q1A). intent: Return the salary value of the employee whose employee number (empno) is 10004
--         for VDB variant V3.
-- 
-- note:
-- the year 1991 is included in variants v3, v4, and v5. we only
-- write the query for these variants for a fair comparison against
-- prima.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (salary^{v_3}) 
--   ((σ (empno=10004) empacct) ⋈_{empacct.title=job.title} job)
-- 
empVQ1, empVQ1_alt, empVQ1_old, empVQ1_alt0, empVQ1_alt1, empVQ1_alt2 :: Algebra
empVQ1 = 
  project (pure $ att2optatt salary_ empv3)
          (join (select empSqlCond $ tRef empacct)
                (tRef job)
                (joinEqCond (att2attrQualRel title_ empacct)
                            (att2attrQualRel title_ job)))

-- π (empno^v_3, salary^v_3)
--   (empacct ⋈_{empacct.title=job.title} job)
-- 
empVQ1_alt =
  project ([att2optatt empno_ empv3
          , att2optatt salary_ empv3])
          (join (tRef empacct)
                (tRef job)
                (joinEqCond (att2attrQualRel title_ empacct)
                            (att2attrQualRel title_ job)))

-- v_3 ⟨π (salary) ((ρ temp (σ (empno=1004) empacct)) ⋈_{temp.title=job.title} job), ε⟩
-- 
empVQ1_alt0 = 
  choice empv3 
         (project (pure $ trueAttr salary_)  
          (join (renameQ temp (select empSqlCond $ tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job))))
         Empty

-- Note that there's a slight difference between empVQ1_old and empVQ1_alt0:
-- the former returns a table that has pres cond of v_3 while the latter
-- returns a table that has a pres cond equal to FM and its only attribute
-- has pres cond of v_3.
-- 
-- π (salary^\{v_3}) ((ρ temp (σ (empno=1004) empacct)) ⋈_{temp.title=job.title} job)
-- 
empVQ1_old = 
  project (pure $ att2optatt salary_ empv3)  
          (join (renameQ temp (select empSqlCond $ tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job)))

-- π (salary^\{v_3}) (σ (empno=1004) (empacct ⋈_{empacct.title=job.title} job))
-- 
empVQ1_alt1 = 
  project (pure $ att2optatt salary_ empv3)  
          (select empSqlCond 
                 (join (tRef empacct)
                       (tRef job)
                       (joinEqCond (att2attrQualRel title_ empacct) (att2attrQualRel title_ job))))

-- v_3 ⟨π (salary) (σ (empno=1004) (empacct ⋈_{empacct.title=job.title} job)), ε ⟩
-- 
empVQ1_alt2 = 
  choice empv3 
         (project (pure $ trueAttr salary_)
                  (select empSqlCond
                          (join (tRef empacct)
                                (tRef job)
                                (joinEqCond (att2attrQualRel title_ empacct) (att2attrQualRel title_ job)))))
         Empty
-- 
-- note: to ensure that naming is correct remove temp from the first, and have an incorrect query to check the system.
-- π (salary^\{v_3}) ((σ (empno=1004) empacct) ⋈_{empacct.title=job.title} job)
empVQ1_alt_typeErr = 
  project (pure $ att2optatt salary_ empv3)  
          (join (select empSqlCond (tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQualRel title_ empacct) (att2attrQualRel title_ job)))

-- 2. intent: Return the salary values of the employee whose employee number (\empno) is 10004, 
--         for VDB variants \vThree\ to \vFive. 
--
-- Note: --> not sure why we need this note!
-- 1. Attribute deptno only exist in v3,v4,v5.
-- 
-- #variants = 3
-- #unique_variants = 2
-- 
-- (v_3 ∨ v_4 ∨ v_5) ⟨π (salary) ((v_3 ∨ v_4)⟨(σ (empno=10004) empacct) 
--                                             ⋈_{empacct.title=job.title} job 
--                                ,σ (empno=10004) empacct⟩), ε⟩
-- 
empVQ2, empVQ2_alt, empVQ2_old, empVQ2_alt_wrong, empVQ2_alt2, empVQ2_alt3_wrong :: Algebra
empVQ2 = 
  choice v345
         (project (pure $ trueAttr salary_)
                  (choice v34
                          (join (select empSqlCond $ tRef empacct)
                                (tRef job)
                                (joinEqCond (att2attrQualRel title_ empacct)
                                            (att2attrQualRel title_ job)))
                          (select empSqlCond $ tRef empacct)))
         Empty

-- (v_3 ∨ v_4 ∨ v_5) ⟨π (empno, salary) ((v_3 ∨ v_4)⟨empacct 
--                                             ⋈_{empacct.title=job.title} job 
--                                ,empacct⟩), ε⟩
-- 
empVQ2_alt = 
  choice v345
         (project ([trueAttr empno_
                  , trueAttr salary_])
                  (choice v34
                          (join (tRef empacct)
                                (tRef job)
                                (joinEqCond (att2attrQualRel title_ empacct)
                                            (att2attrQualRel title_ job)))
                          (tRef empacct)))
         Empty

-- π (salary^{v_3 ∨ v_4 ∨ v_5}) (v_3 ∨ v_4 ⟨ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} job,
--                                          σ (empno=10004) empactt⟩)
empVQ2_old = 
  project (pure $ att2optatt salary_ (F.Or (F.Or empv3 empv4) empv5))
          (choice v34
                  q1
                  q2)
    where
      q1 = join (renameQ temp q2)
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job))
      q2 = (select empSqlCond $ tRef empacct)

-- π (salary) (v_3 ∨ v_4 ⟨ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} job,
--                        v_5 ⟨σ (empno=10004) empactt, ε ⟩⟩)
-- 
-- Note: this is wrong because it results in π (..) ε for some configs.
-- which is ill-typed and incorrect. 
empVQ2_alt_wrong = 
  project (pure $ trueAttr salary_)
          (choice v34
                  q1
                  (choice empv5 q2 Empty))
    where
      q1 = join (renameQ temp q2)
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job))
      q2 = (select empSqlCond $ tRef empacct)


-- π (salary^{v_3 ∨ v_4 ∨ v_5}) 
--   (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} 
--    v_3 ∨ v_4 ⟨job, ε⟩)
-- 
empVQ2_alt2 = 
  project (pure $ att2optatt salary_ v345)
          (join q1
                (choice (F.Or empv3 empv4) (tRef job) Empty)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job)))
    where
      q1 = renameQ temp (select empSqlCond $ tRef empacct)

-- π (salary) 
--   (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} 
--    v_3 ∨ v_4 ⟨job, ε⟩)
-- 
-- Note: it's wrong for the same reason as empvq2_alt_wrong
empVQ2_alt3_wrong = 
  project (pure $ trueAttr salary_)
          (join q1 
                (choice v34 (tRef job) Empty)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job)))
    where
      q1 = renameQ temp (select empSqlCond $ tRef empacct)


-- 3.intent: Return the manager's name (of department d001) for VDB variant V3. 
-- 
-- #variants = 1?
-- #unique_variants = 1?
-- 
-- π (name^v_3) ((σ (deptno="d001") empacct)
--               ⋈_{empacct.empno=dept.managerno} dept)
-- 
empVQ3, empVQ3_alt, empVQ3_old :: Algebra
empVQ3 = 
  project (pure $ att2optatt name_ empv3)
          (join (select (eqAttValSqlCond deptno_ departno_value)
                        (tRef empacct))
                (tRef dept)
                (joinEqCond (att2attrQualRel empno_ empacct)
                            (att2attrQualRel managerno_ dept)))

-- π (deptno^v_3, name^v_3) (empacct
--               ⋈_{empacct.empno=dept.managerno} dept)
-- 
empVQ3_alt = 
  project ([att2optatt deptno_ empv3
          , att2optatt name_ empv3])
          (join (tRef empacct)
                (tRef dept)
                (joinEqCond (att2attrQualRel empno_ empacct)
                            (att2attrQualRel managerno_ dept)))

-- v_3 ⟨π (name) ((ρ (temp) (σ (deptno=d001) empacct)) ⋈_{temp.empno=dept.managerno} dept), ε⟩ 
-- 
empVQ3_old = 
  -- choice empv3 
         (project (pure $ att2optatt name_ empv3)
                  (join (renameQ temp 
                                 (select (eqAttValSqlCond deptno_ departno_value)
                                         (tRef empacct)))
                        (tRef dept)
                        (joinEqCond (att2attrQual empno_ temp) (att2attrQualRel managerno_ dept) )))
         -- Empty


-- 4.intent: Return the manager's name (of department d001), for VDB variants \vThree\ to \vFive.
-- 
-- #variants = 3
-- #unique_variants = 2 but it should be 3
-- 
-- v_3 ∨ v_4 ∨ v_5 ⟨π (name, firstname, lastname) 
--                    (v_3⟨empacct, empbio⟩ ⋈_{empno=managerno} 
--                                          σ (deptno="d001") dept, ε⟩
-- 
-- Note: differences in #unique_variants is due to the fact that schema hasn't been 
-- pushed yet!
-- 
empVQ4, empVQ4_alt1 :: Algebra
empVQ4 = 
  choice v345
         (project ([trueAttr name_, 
                    trueAttr firstname_, 
                    trueAttr lastname_])
                  (join (choice empv3
                               (tRef empacct)
                               (tRef empbio))
                        (select (eqAttValSqlCond deptno_ departno_value)
                                (tRef dept))
                        (joinEqCond (att2attr empno_) (att2attr managerno_))))
         Empty

-- v_3 ∨ v_4 ∨ v_5 ⟨π (name^{v_3 ∨ v_4}, firstname^{v_5}, lastname^{v_5}) 
--                    (v_3⟨empacct, empbio⟩ ⋈_{empno=managerno} 
--                                          σ (deptno="d001") dept, ε⟩
-- 
-- Note: it has #unique_variants = 4!
empVQ4_alt1 =
  choice v345
         (project ([att2optatt name_ v34, 
                    att2optatt firstname_ empv5, 
                    att2optatt lastname_ empv5])
                  (join (choice empv3
                               (tRef empacct)
                               (tRef empbio))
                        (select (eqAttValSqlCond deptno_ departno_value)
                                (tRef dept))
                        (joinEqCond (att2attr empno_) (att2attr managerno_))))
         Empty

-- 5.intent: Find all managers that the employee 10004 worked with, for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- v_3⟨π (managerno) (ρ (temp) (σ (empno=10004) empacct) 
--                       ⋈_{temp.deptno=dept.deptno} dept), ε⟩
-- 
empVQ5 :: Algebra
empVQ5 = 
  -- choice empv3 
         (project (pure $ att2optatt managerno_ empv3)
                  (join (renameQ temp (select empSqlCond (tRef empacct)))
                        (tRef dept)
                        (joinEqCond (att2attrQual deptno_ temp) (att2attrQualRel deptno_ dept))))
         -- Empty

-- 6.intent: Find all managers that employee 10004 worked with, for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 1
-- 
-- v_3 ∨ v_4 ∨ v_5 ⟨π (managerno) (ρ (temp) (σ (empno=10004) empacct) 
--                    ⋈_{temp.deptno=dept.deptno} dept), ε⟩
-- 
empVQ6 :: Algebra
empVQ6 = 
  -- choice v345
         (project (pure $ att2optatt managerno_ v345)
                  (join (renameQ temp (select empSqlCond (tRef empacct)))
                        (tRef dept)
                        (joinEqCond (att2attrQual deptno_ temp) (att2attrQualRel deptno_ dept))))
         -- Empty

-- 7.intent: Find all salary values of managers, during the period of manager appointment, for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (managerno^{v_3}, salary^{v_3})
--   (dept ⋈_{managerno=empno}
--         (empacct ⋈_{empacct.title=job.title} job))
-- 
empVQ7 :: Algebra
empVQ7 = 
  project ([att2optatt managerno_ empv3
          , att2optatt salary_ empv3])
          (join (tRef dept)
                (joinTwoRels empacct job title_)
                (joinEqCond (att2attr managerno_) (att2attr empno_)))

-- 8.intent: Find all salary values of managers, during the period of manager appointment, for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 2
-- 
-- π (managerno, name)
--   (ρ (temp) (empacct ⋈_{mangerno=empno} dept))
--                     ⋈_{temp.title=job.title} (v_3 ∨ v_4 ⟨job,ε ⟩))
-- 
empVQ8, empVQ8_wrong :: Algebra
empVQ8 = 
  project ([att2optatt managerno_ v345
          , att2optatt name_ v345])
                  (join (renameQ temp 
                                 (join (tRef empacct) 
                                       (tRef dept) 
                                       (joinEqCond managerno empno)))
                        (choice v34 
                                (tRef job)
                                Empty)
                        (joinEqCond (att2attrQual title_ temp) 
                                    (att2attrQualRel title_ dept)))

-- π (managerno, name)
--   (v_3 ∨ v_4 ∨ v_5 ⟨(ρ (temp) (empacct ⋈_{mangerno=empno} dept))
--                     ⋈_{temp.title=job.title} (v_3 ∨ v_4 ⟨job,ε ⟩), ε⟩)
-- Note: it's wrong b/c it generates a query π (..) ε.
-- this affect #unique_variants = 3.
empVQ8_wrong = 
  project ([att2optatt managerno_ v345
          , att2optatt name_ v345])
          (choice v345 
                  (join (renameQ temp 
                                 (join (tRef empacct) 
                                       (tRef dept) 
                                       (joinEqCond managerno empno)))
                        (choice v34 
                                (tRef job)
                                Empty)
                        (joinEqCond (att2attrQual title_ temp) 
                                    (att2attrQualRel title_ dept)))
                  Empty)

-- 11.intent: For all managers that the employee, whose employee number (\empno) is 10004, has worked with, 
--            find all the departments that the manager managed, for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- temp0 = ρ (temp0) 
--           (π (managerno, deptno)
--              (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.deptno=dept.deptno} dept))
-- π (managerno^{v_3}, deptno^{v_3})
--   (temp0 ⋈_{temp0.managerno=dept.mangerno} dept)
-- 
empVQ11 :: Algebra
empVQ11 = 
  project ([att2optattQualRel managerno_ dept empv3
          , att2optattQualRel deptno_ dept empv3])
          (join temp0
                (tRef dept)
                (joinEqCond (att2attrQual managerno_ "temp0") 
                            (att2attrQualRel managerno_ dept)))
    where
      temp0 =
        renameQ "temp0" 
                (project ([trueAttr managerno_
                         , trueAttrQualRel deptno_ dept])
                        (join (renameQ temp (select empSqlCond (tRef empacct)))
                              (tRef dept)
                              (joinEqCond (att2attrQual deptno_ temp) 
                                          (att2attrQualRel deptno_ dept))))

-- 12.intent: For all managers that the employee, whose employee number (\empno) is 10004, has worked with, 
--            find all the departments that the manager managed, for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 1
-- 
-- temp0 = ρ (temp0) 
--           (π (managerno, deptno)
--              (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.deptno=dept.deptno} dept))
-- π (managerno^{v_3 ∨ v_4 ∨ v_5}, deptno^{v_3 ∨ v_4 ∨ v_5})
--   (temp0 ⋈_{temp0.managerno=dept.mangerno} dept)
-- 
empVQ12 :: Algebra
empVQ12 = 
  project ([att2optattQualRel managerno_ dept v345
          , att2optattQualRel deptno_ dept v345])
          (join temp0
                (tRef dept)
                (joinEqCond (att2attrQual managerno_ "temp0") 
                            (att2attrQualRel managerno_ dept)))
    where
      temp0 =
        renameQ "temp0" 
                (project ([trueAttr managerno_
                         , trueAttrQualRel deptno_ dept])
                        (join (renameQ temp (select empSqlCond (tRef empacct)))
                              (tRef dept)
                              (joinEqCond (att2attrQual deptno_ temp) 
                                          (att2attrQualRel deptno_ dept))))

-- 13.intent: For all managers, find all managers in the department that he/she worked in, 
--            for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (temp.managerno^{v_3}, deptname^{v_3}, dept.managerno^{v_3})
--   ((ρ (temp) (π (managerno, deptno) dept)) ⋈_{temp.deptno=dept.deptno} dept)
-- 
empVQ13 :: Algebra
empVQ13 = 
  project ([att2optattQual managerno_ temp empv3
          , att2optatt deptname_ empv3
          , att2optattQualRel managerno_ dept empv3])
          (join (renameQ temp 
                         (project ([trueAttr managerno_, trueAttr deptno_])
                                  (tRef dept)))
                (tRef dept)
                (joinEqCond (att2attrQual deptno_ temp) 
                            (att2attrQualRel deptno_ dept)))

-- 14.intent: For all managers, find all managers in the department that he/she worked in, 
--            for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 1
-- 
-- π (temp.managerno^{v_3 ∨ v_4 ∨ v_5}
--    , deptname^{v_3 ∨ v_4 ∨ v_5}
--    , dept.managerno^{v_3 ∨ v_4 ∨ v_5})
--   ((ρ (temp) (π (managerno, deptno) dept)) ⋈_{temp.deptno=dept.deptno} dept)
-- 
empVQ14 :: Algebra
empVQ14 = 
  project ([att2optattQual managerno_ temp v345
          , att2optatt deptname_ v345
          , att2optattQualRel managerno_ dept v345])
          (join (renameQ temp 
                         (project ([trueAttr managerno_, trueAttr deptno_])
                                  (tRef dept)))
                (tRef dept)
                (joinEqCond (att2attrQual deptno_ temp) 
                            (att2attrQualRel deptno_ dept)))
