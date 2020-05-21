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

-- The alternative queries (named as q_alt) are for runtime test.

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
empVQ1, empVQ1_alt :: Algebra
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


-- 2. intent: Return the salary values of the employee whose employee number (\empno) is 10004, 
--         for VDB variants \vThree\ to \vFive. 
-- 
-- #variants = 3
-- #unique_variants = 2
-- 
-- (v_3 ∨ v_4 ∨ v_5) ⟨π (salary) ((v_3 ∨ v_4)⟨(σ (empno=10004) empacct) 
--                                             ⋈_{empacct.title=job.title} job 
--                                ,σ (empno=10004) empacct⟩), ε⟩
-- 
empVQ2, empVQ2_alt :: Algebra
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

-- 3.intent: Return the manager's name (of department d001) for VDB variant V3. 
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (name^v_3) ((σ (deptno="d001") empacct)
--               ⋈_{empacct.empno=dept.managerno} dept)
-- 
empVQ3, empVQ3_alt :: Algebra
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

-- 4.intent: Return the manager's name (of department d001), for VDB variants \vThree\ to \vFive.
-- 
-- #variants = 3
-- #unique_variants = 3
-- 
-- v_3 ∨ v_4 ∨ v_5 ⟨π (name, firstname, lastname)
--                    (v_3 ⟨empacct, empbio⟩ ⋈_{empno=managerno} (σ (deptno="d001") dept)), ε⟩
-- 
empVQ4, empVQ4_alt :: Algebra
empVQ4 = 
  choice v345
         (project (fmap trueAttr [name_, firstname_, lastname_])
                  (join (choice empv3 (tRef empacct) (tRef empbio))
                        (select (eqAttValSqlCond deptno_ departno_value) (tRef dept))
                        (joinEqCond (att2attr empno_)
                                    (att2attr managerno_))))
         Empty

-- v_3 ∨ v_4 ∨ v_5 ⟨π (deptno, name, firstname, lastname)
--                    (v_3 ⟨empacct, empbio⟩ ⋈_{empno=managerno} dept), ε⟩
-- 
empVQ4_alt = 
  choice v345
         (project (fmap trueAttr [name_, firstname_, lastname_])
                  (join (choice empv3 (tRef empacct) (tRef empbio))
                        (tRef dept)
                        (joinEqCond (att2attr empno_)
                                    (att2attr managerno_))))
         Empty

-- 5.intent: Find all managers that the employee 10004 worked with, for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (managerno^v_3) ((σ (deptno="d001") empacct) ⋈_{empacct.empno=dept.managerno} dept)
-- 
empVQ5, empVQ5_alt :: Algebra
empVQ5 = 
  project (pure $ att2optatt name_ empv3)
          (join (select (eqAttValSqlCond deptno_ departno_value)
                        (tRef empacct))
                (tRef dept)
                (joinEqCond (att2attrQualRel empno_ empacct)
                            (att2attrQualRel managerno_ dept)))

-- π (deptno^v_3, managerno^v_3) (empacct ⋈_{empacct.empno=dept.managerno} dept)
-- 
empVQ5_alt = 
  project (fmap (flip att2optatt empv3) [deptno_, name_])
          (join (tRef empacct)
                (tRef dept)
                (joinEqCond (att2attrQualRel empno_ empacct)
                            (att2attrQualRel managerno_ dept)))


-- 6.intent: Find all managers that employee 10004 worked with, for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 1
-- 
-- π (managerno^{v_3 ∨ v_4 ∨ v_5}) ((σ (empno=10004) empacct) 
--                                  ⋈_{empacct.deptno=dept.deptno} dept)
-- 
empVQ6, empVQ6_alt :: Algebra
empVQ6 = 
  project (pure $ att2optatt managerno_ v345)
          (join (select empSqlCond (tRef empacct))
                (tRef dept)
                (joinEqCond (att2attrQualRel deptno_ empacct)
                            (att2attrQualRel deptno_ dept)))

-- π (empno^{v_3 ∨ v_4 ∨ v_5}, managerno^{v_3 ∨ v_4 ∨ v_5}) 
--   (empacct ⋈_{empacct.deptno=dept.deptno} dept)
-- 
empVQ6_alt = 
  project (fmap (flip att2optatt v345) [empno_, managerno_])
          (join (tRef empacct)
                (tRef dept)
                (joinEqCond (att2attrQualRel deptno_ empacct)
                            (att2attrQualRel deptno_ dept)))

-- 7.intent: Find all salary values of managers, during the period of manager appointment, for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (managerno^v_3, salary^v_3) (dept 
--                               ⋈_{managerno=empno} (empacct 
--                                                   ⋈_{empacct.title=job.title} job))
-- 
empVQ7, empVQ7_alt :: Algebra
empVQ7 = 
  project (fmap (flip att2optatt empv3) [managerno_, salary_])
          (join (tRef dept)
                (join (tRef empacct)
                      (tRef job)
                      (joinEqCond (att2attrQualRel title_ empacct)
                                  (att2attrQualRel title_ job)))
                (joinEqCond (att2attr managerno_)
                            (att2attr empno_)))

-- π (managerno^v_3, salary^v_3) (dept 
--                               ⋈_{managerno=empno} (empacct 
--                                                   ⋈_{empacct.title=job.title} job))
-- 
empVQ7_alt = empVQ7

-- 8.intent: Find all salary values of managers, during the period of manager appointment, for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 2
-- 
-- v_3 ∨ v_4 ∨ v_5 ⟨π (managerno, name) 
--                    (v_3 ∨ v_4 ⟨(empacct ⋈_{managerno=empno} dept) 
--                                ⋈_{empacct.title=job.title} job,
--                        empacct ⋈_{managerno=empno} dept⟩), ε⟩
-- 
empVQ8, empVQ8_alt :: Algebra
empVQ8 = 
  choice v345
         (project (fmap trueAttr [managerno_, name_])
                  (choice v34
                          (join (join (tRef empacct)
                                      (tRef dept)
                                      (joinEqCond (att2attr managerno_)
                                                  (att2attr empno_)))
                                (tRef job)
                                (joinEqCond (att2attrQualRel title_ empacct)
                                            (att2attrQualRel title_ job)))
                          (join (tRef empacct)
                                (tRef dept)
                                (joinEqCond (att2attr managerno_)
                                            (att2attr empno_)))))
         Empty

-- v_3 ∨ v_4 ∨ v_5 ⟨π (managerno, name) 
--                    (v_3 ∨ v_4 ⟨(empacct ⋈_{managerno=empno} dept) 
--                                ⋈_{empacct.title=job.title} job,
--                        empacct ⋈_{managerno=empno} dept⟩), ε⟩
-- 
empVQ8_alt = empVQ8

-- 11.intent: For all managers that the employee, whose employee number (\empno) is 10004, has worked with, 
--            find all the departments that the manager managed, for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- tempQ = ρ (temp) 
--           (π (managerno, deptno)
--              (σ (empno=10004) empacct) ⋈_{empacct.deptno=dept.deptno} dept))
-- π (dept.managerno^{v_3}, dept.deptno^{v_3})
--   (tempQ ⋈_{temp.managerno=dept.mangerno} dept)
-- 
empVQ11, empVQ11_alt :: Algebra
empVQ11 = 
  project ([att2optattQualRel managerno_ dept empv3
          , att2optattQualRel deptno_ dept empv3])
          (join tempQ
                (tRef dept)
                (joinEqCond (att2attrQual managerno_ temp) 
                            (att2attrQualRel managerno_ dept)))
    where
      tempQ =
        renameQ temp 
                (project ([trueAttr managerno_
                         , trueAttrQualRel deptno_ dept])
                        (join (select empSqlCond (tRef empacct))
                              (tRef dept)
                              (joinEqCond (att2attrQualRel deptno_ empacct) 
                                          (att2attrQualRel deptno_ dept))))

-- 
-- 
empVQ11_alt = empVQ11

-- 12.intent: For all managers that the employee, whose employee number (\empno) is 10004, has worked with, 
--            find all the departments that the manager managed, for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 1
-- 
-- tempQ = ρ (temp) 
--           (π (managerno, deptno)
--              (σ (empno=10004) empacct) ⋈_{empacct.deptno=dept.deptno} dept))
-- π (dept.managerno^{v_3 ∨ v_4 ∨ v_5}, dept.deptno^{v_3 ∨ v_4 ∨ v_5})
--   (tempQ ⋈_{temp.managerno=dept.mangerno} dept)
-- 
empVQ12, empVQ12_alt :: Algebra
empVQ12 = 
  project ([att2optattQualRel managerno_ dept v345
          , att2optattQualRel deptno_ dept v345])
          (join tempQ
                (tRef dept)
                (joinEqCond (att2attrQual managerno_ temp) 
                            (att2attrQualRel managerno_ dept)))
    where
      tempQ =
        renameQ temp 
                (project ([trueAttr managerno_
                         , trueAttrQualRel deptno_ dept])
                        (join (select empSqlCond (tRef empacct))
                              (tRef dept)
                              (joinEqCond (att2attrQualRel deptno_ empacct) 
                                          (att2attrQualRel deptno_ dept))))

-- 
-- 
empVQ12_alt = empVQ12

-- 13.intent: For all managers, find all managers in the department that he/she worked in, 
--            for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (temp.managerno^{v_3}, deptname^{v_3}, dept.managerno^{v_3})
--   ((ρ (temp) (π (managerno, deptno) dept)) ⋈_{temp.deptno=dept.deptno} dept)
-- 
empVQ13, empVQ13_alt :: Algebra
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

empVQ13_alt = empVQ13

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
empVQ14, empVQ14_alt :: Algebra
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

empVQ14_alt = empVQ14