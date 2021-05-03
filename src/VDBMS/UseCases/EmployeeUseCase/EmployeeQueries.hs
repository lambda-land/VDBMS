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

-- for test
import Data.Map (fromList)
import VDBMS.DBMS.Value.Type

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

-- empQppr = project 
--   [att2optatt empno_ v45, trueAttr name_, trueAttr firstname_, trueAttr lastname_]
--   (tRef empbio)

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
-- after pushing schema: #variants = 1
-- after pushing schema: #unique_variants = 6
-- 
-- π (salary^{v_3}) 
--   (σ (empno=10004) (empacct ⋈_{empacct.title=job.title} job))
-- 
-- emptest :: Algebra
-- emptest = project (pure $ trueAttr salary_) (tRef job)

-- vtest :: F.FeatureExpr
-- vtest = foldr F.Or v34 [empv1,empv2]

-- tbltest = (vtest,fromList [(Attribute {attributeName = "salary"},(F.Lit True,TInt32)),(Attribute {attributeName = "title"},(F.Lit True,TString))])
empVQ1, empVQ1_alt, empVQ1_old, empVQ1_alt0, empVQ1_alt1, empVQ1_alt2 :: Algebra
empVQ1' = 
  project (pure $ att2optatt salary_ empv3)
          (join (select empSqlCond $ tRef empacct)
                (tRef job)
                (joinEqCond (att2attrQualRel title_ empacct)
                            (att2attrQualRel title_ job)))
empVQ1 = 
  project (pure $ att2optattQualRel salary_ job empv3)
          (select empSqlCond (join (tRef empacct)
                (tRef job)
                (joinEqCond (att2attrQualRel title_ empacct)
                            (att2attrQualRel title_ job))))

-- π (empno^v_3, salary^v_3)
--   (empacct ⋈_{empacct.title=job.title} job)
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 1
-- after pushing schema: #unique_variants = 
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
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ1_alt0 = 
  choice empv3 
         (project (pure $ trueAttr salary_)  
          (join (renameQ temp (select empSqlCond $ tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) 
                            (att2attrQualRel title_ job))))
         Empty

-- Note that there's a slight difference between empVQ1_old and empVQ1_alt0:
-- the former returns a table that has pres cond of v_3 while the latter
-- returns a table that has a pres cond equal to FM and its only attribute
-- has pres cond of v_3. --> actually they both have the same type since
-- the choice affects each branch separately and doesn't have the pc v3
-- over the entire type env.
-- 
-- π (salary^\{v_3}) ((ρ temp (σ (empno=1004) empacct)) ⋈_{temp.title=job.title} job)
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 1
-- after pushing schema: #unique_variants = 
-- 
empVQ1_old = 
  project (pure $ att2optatt salary_ empv3)  
          (join (renameQ temp (select empSqlCond $ tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQual title_ temp) 
                            (att2attrQualRel title_ job)))

-- π (salary^\{v_3}) (σ (empno=1004) (empacct ⋈_{empacct.title=job.title} job))
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 1
-- after pushing schema: #unique_variants = 
-- 
empVQ1_alt1 = 
  project (pure $ att2optatt salary_ empv3)  
          (select empSqlCond 
                 (join (tRef empacct)
                       (tRef job)
                       (joinEqCond (att2attrQualRel title_ empacct) 
                                   (att2attrQualRel title_ job))))

-- v_3 ⟨π (salary) (σ (empno=1004) (empacct ⋈_{empacct.title=job.title} job)), ε ⟩
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 1
-- after pushing schema: #unique_variants = 
-- 
empVQ1_alt2 = 
  choice empv3 
         (project (pure $ trueAttr salary_)
                  (select empSqlCond
                          (join (tRef empacct)
                                (tRef job)
                                (joinEqCond (att2attrQualRel title_ empacct) 
                                            (att2attrQualRel title_ job)))))
         Empty

-- 
-- note: to ensure that naming is correct remove temp from the first, 
-- and have an incorrect query to check the system.
-- 
-- π (salary^\{v_3}) ((σ (empno=1004) empacct) ⋈_{empacct.title=job.title} job)
-- 
-- actually this is type correct b/c there's no need to rename the select empsqlcond
-- subquery since in the type env title has two qualifiers one is empacct and 
-- the other is job. so this will be fine.
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ1_alt_typeErr = 
  project (pure $ att2optatt salary_ empv3)  
          (join (select empSqlCond (tRef empacct))
                (tRef job)
                (joinEqCond (att2attrQualRel title_ empacct) 
                            (att2attrQualRel title_ job)))

-- 2. intent: Return the salary values of the employee whose employee number (\empno) is 10004, 
--         for VDB variants \vThree\ to \vFive. 
--
-- Note: --> not sure why we need this note!
-- 1. Attribute deptno only exist in v3,v4,v5.
-- 
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- (v_3 ∨ v_4 ∨ v_5) ⟨π (salary) ((v_3 ∨ v_4)⟨σ (empno=10004) (empacct
--                                             ⋈_{empacct.title=job.title} job)
--                                ,σ (empno=10004) empacct⟩), ε⟩
-- 
empVQ2, empVQ2_alt, empVQ2_old, empVQ2_alt_thought_wrong_but_correct, empVQ2_alt2, empVQ2_alt3_thought_wrong_but_correct :: Algebra
empVQ2 = 
  choice v345
         (project (pure $ trueAttr salary_)
                  (choice v34
                          (select empSqlCond 
                                  (join (tRef empacct)
                                        (tRef job)
                                        (joinEqCond (att2attrQualRel title_ empacct)
                                                    (att2attrQualRel title_ job))))
                          (select empSqlCond $ tRef empacct)))
         Empty

-- empvq2lchc =
--   (project (pure $ trueAttr salary_)
--                   (choice v34
--                           (join (select empSqlCond $ tRef empacct)
--                                 (tRef job)
--                                 (joinEqCond (att2attrQualRel title_ empacct)
--                                             (att2attrQualRel title_ job)))
--                           (select empSqlCond $ tRef empacct)))

-- empvq2tst = 
--   choice v345
--                   (choice v34
--                           (join (select empSqlCond $ tRef empacct)
--                                 (tRef job)
--                                 (joinEqCond (att2attrQualRel title_ empacct)
--                                             (att2attrQualRel title_ job)))
--                           (select empSqlCond $ tRef empacct))
--          Empty

-- this should give ambg attr. no it shouldn't because the attribute salary only
-- exists in empacct for version5 while the relation job doesn't exists in that
-- version. thus the attribute salary gets dropped since the conjunction
-- of the fexps of the two joined relations will be applied to attributes. 
-- empvq2l = project (pure $ trueAttr salary_) (join (select empSqlCond $ tRef empacct)
--                                 (tRef job)
--                                 (joinEqCond (att2attrQualRel title_ empacct)
--                                             (att2attrQualRel title_ job)))
-- empvq2r = project (pure $ trueAttr salary_)( tRef empacct)

-- (v_3 ∨ v_4 ∨ v_5) ⟨π (empno, salary) ((v_3 ∨ v_4)⟨empacct 
--                                             ⋈_{empacct.title=job.title} job 
--                                ,empacct⟩), ε⟩
-- 
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
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
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
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

-- empProj = project (pure $ trueAttr salary_) Empty

-- π (salary) (v_3 ∨ v_4 ⟨ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.title=job.title} job,
--                        v_5 ⟨σ (empno=10004) empactt, ε ⟩⟩)
-- 
-- Note: this is wrong because it results in π (..) ε for some configs.
-- which is ill-typed and incorrect. --> actually this is not type incorrect.
-- b/c the type env is union of the left and right branch of the choice
-- which isn't empty. so it's different than projecting an attribute from empty.
-- 
-- #variants = 3 
-- have to push schema onto it for the correct number of vars.
-- #unique_variants = 5 after push sch
-- , 3 before push sch--> TODO look into this
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ2_alt_thought_wrong_but_correct = 
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
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
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
-- Note: it's wrong for the same reason as empvq2_alt_wrong --> it is not!
-- #variants = 3 
-- have to push schema onto it for the correct number of vars.
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ2_alt3_thought_wrong_but_correct = 
  project (pure $ trueAttr salary_)
          (join q1 
                (choice v34 (tRef job) Empty)
                (joinEqCond (att2attrQual title_ temp) (att2attrQualRel title_ job)))
    where
      q1 = renameQ temp (select empSqlCond $ tRef empacct)


-- 3.intent: Return the manager's name (of department d001) for VDB variant V3. 
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- π (name^v_3) (σ (deptno="d001") (empacct
--               ⋈_{empacct.empno=dept.managerno} dept))
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ3, empVQ3_alt, empVQ3_old :: Algebra
empVQ3 = 
  project (pure $ att2optatt name_ empv3)
          (select (eqAttValSqlCond deptno_ departno_value)
                  (join (tRef empacct)
                         (tRef dept)
                         (joinEqCond (att2attrQualRel empno_ empacct)
                                     (att2attrQualRel managerno_ dept))))

empvq3tst = (select (eqAttValSqlCond deptno_ departno_value)
                        (tRef empacct))

-- π (deptno^v_3, name^v_3) (empacct
--               ⋈_{empacct.empno=dept.managerno} dept)
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
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
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
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
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- v_3 ∨ v_4 ∨ v_5 ⟨π (name, firstname, lastname) (σ (deptno="d001")
--                    (v_3 ⟨empacct, empbio⟩ ⋈_{empno=managerno}  dept), ε⟩
-- 
empVQ4, empVQ4_alt, empVQ4_old, empVQ4_alt1 :: Algebra
empVQ4 = 
  choice v345
         (project (fmap trueAttr [name_, firstname_, lastname_])
                  (select (eqAttValSqlCond deptno_ departno_value)
                          (join (choice empv3 (tRef empacct) (tRef empbio))
                                (tRef dept)
                                (joinEqCond (att2attr empno_)
                                            (att2attr managerno_)))))
         Empty

-- v_3 ∨ v_4 ∨ v_5 ⟨π (deptno, name, firstname, lastname)
--                    (v_3 ⟨empacct, empbio⟩ ⋈_{empno=managerno} dept), ε⟩
-- 
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ4_alt = 
  choice v345
         (project (fmap trueAttr [name_, firstname_, lastname_])
                  (join (choice empv3 (tRef empacct) (tRef empbio))
                        (tRef dept)
                        (joinEqCond (att2attr empno_)
                                    (att2attr managerno_))))
         Empty

-- v_3 ∨ v_4 ∨ v_5 ⟨π (name, firstname, lastname) 
--                    (v_3⟨empacct, empbio⟩ ⋈_{empno=managerno} 
--                                          σ (deptno="d001") dept, ε⟩
-- 
-- Note: differences in #unique_variants is due to the fact that schema hasn't been 
-- pushed yet!
-- 
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ4_old = 
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
-- #variants = 3
-- #unique_variants = 4
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
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
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- π (managerno^v_3) (σ (deptno="d001") (empacct ⋈_{empacct.empno=dept.managerno} dept)
-- 
empVQ5, empVQ5_alt, empVQ5_old :: Algebra
empVQ5 = 
  project (pure $ att2optatt name_ empv3)
          (select (eqAttValSqlCond deptno_ departno_value)
                  (join (tRef empacct)
                        (tRef dept)
                        (joinEqCond (att2attrQualRel empno_ empacct)
                                    (att2attrQualRel managerno_ dept))))

-- π (deptno^v_3, managerno^v_3) (empacct ⋈_{empacct.empno=dept.managerno} dept)
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ5_alt = 
  project [att2optatt managerno_ empv3
          , att2optattQualRel deptno_ dept empv3]
          (join (tRef empacct)
                (tRef dept)
                (joinEqCond (att2attrQualRel empno_ empacct)
                            (att2attrQualRel managerno_ dept)))

-- v_3⟨π (managerno) (ρ (temp) (σ (empno=10004) empacct) 
--                       ⋈_{temp.deptno=dept.deptno} dept), ε⟩
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ5_old = 
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
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- π (managerno^{v_3 ∨ v_4 ∨ v_5}) (σ (empno=10004) (empacct
--                                  ⋈_{empacct.deptno=dept.deptno} dept))
-- 
empVQ6, empVQ6_alt, empVQ6_old :: Algebra
empVQ6 = 
  project (pure $ att2optatt managerno_ v345)
          (select empSqlCond 
                  (join (tRef empacct)
                        (tRef dept)
                        (joinEqCond (att2attrQualRel deptno_ empacct)
                                    (att2attrQualRel deptno_ dept))))

-- π (empno^{v_3 ∨ v_4 ∨ v_5}, managerno^{v_3 ∨ v_4 ∨ v_5}) 
--   (empacct ⋈_{empacct.deptno=dept.deptno} dept)
-- 
-- #variants = 3
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ6_alt = 
  project (fmap (flip att2optatt v345) [empno_, managerno_])
          (join (tRef empacct)
                (tRef dept)
                (joinEqCond (att2attrQualRel deptno_ empacct)
                            (att2attrQualRel deptno_ dept)))

-- v_3 ∨ v_4 ∨ v_5 ⟨π (managerno) (ρ (temp) (σ (empno=10004) empacct) 
--                    ⋈_{temp.deptno=dept.deptno} dept), ε⟩
-- #variants = 3
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ6_old = 
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
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- π (managerno^v_3, salary^v_3) (dept 
--                               ⋈_{managerno=empno} (empacct 
--                                                   ⋈_{empacct.title=job.title} job))
-- 
empVQ7, empVQ7_alt, empVQ7_old :: Algebra
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
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ7_alt = empVQ7

-- π (managerno^{v_3}, salary^{v_3})
--   (dept ⋈_{managerno=empno}
--         (empacct ⋈_{empacct.title=job.title} job))
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ7_old = 
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
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- v_3 ∨ v_4 ∨ v_5 ⟨π (managerno, name) 
--                    (v_3 ∨ v_4 ⟨(empacct ⋈_{managerno=empno} dept) 
--                                ⋈_{empacct.title=job.title} job,
--                        empacct ⋈_{managerno=empno} dept⟩), ε⟩
-- 
empVQ8, empVQ8_alt, empVQ8_old_thought_wrong_but_correct, empVQ8_thought_wrong_but_correct :: Algebra
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
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ8_alt = empVQ8

-- π (managerno, name)
--   (ρ (temp) (empacct ⋈_{mangerno=empno} dept))
--                     ⋈_{temp.title=job.title} (v_3 ∨ v_4 ⟨job,ε ⟩))
-- 
-- Note: it's wrong because it's joining with empty! --> wrong!
-- actually it's type correct since join unions the left and 
-- right of the choice and if one is empty the type env
-- has the extra stuff from the outside of choice. 
-- in this example the stuff from temp.
-- 
-- #variants = 3
-- #unique_variants = 2
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ8_old_thought_wrong_but_correct = 
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
                                    (att2attrQualRel title_ job)))

-- π (managerno, name)
--   (v_3 ∨ v_4 ∨ v_5 ⟨(ρ (temp) (empacct ⋈_{mangerno=empno} dept))
--                     ⋈_{temp.title=job.title} (v_3 ∨ v_4 ⟨job,ε ⟩), ε⟩)
-- Note: it's wrong b/c it generates a query π (..) ε. --> wrong
-- it's type correct. talked about this in empvq2.
-- this affect #unique_variants = 3. 
-- 
-- #variants = 3
-- #unique_variants = 3
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ8_thought_wrong_but_correct = 
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
                                    (att2attrQualRel title_ job)))
                  Empty)

-- 11.intent: For all managers that the employee, whose employee number (\empno) is 10004, has worked with, 
--            find all the departments that the manager managed, for VDB variant \vThree. 
--
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- tempQ = ρ (temp) 
--           (π (managerno, deptno)
--              (σ (empno=10004) (empacct ⋈_{empacct.deptno=dept.deptno} dept))
-- π (managerno^{v_3}, deptno^{v_3})
--   (tempQ ⋈_{temp.managerno=dept.mangerno} dept)
-- 
empVQ11, empVQ11_alt, empVQ11_old :: Algebra
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
                        (select empSqlCond 
                                (join (tRef empacct)
                                      (tRef dept)
                                      (joinEqCond (att2attrQualRel deptno_ empacct) 
                                                  (att2attrQualRel deptno_ dept)))))

-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ11_alt = empVQ11

-- temp0 = ρ (temp0) 
--           (π (managerno, deptno)
--              (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.deptno=dept.deptno} dept))
-- π (managerno^{v_3}, deptno^{v_3})
--   (temp0 ⋈_{temp0.managerno=dept.mangerno} dept)
-- 
-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ11_old = 
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
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
-- tempQ = ρ (temp) 
--           (π (managerno, deptno)
--              (σ (empno=10004) (empacct ⋈_{empacct.deptno=dept.deptno} dept))
-- π (managerno^{v_3 ∨ v_4 ∨ v_5}, deptno^{v_3 ∨ v_4 ∨ v_5})
--   (tempQ ⋈_{temp.managerno=dept.mangerno} dept)
-- 
empVQ12, empVQ12_alt, empVQ12_old :: Algebra
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
                        (select empSqlCond 
                                (join (tRef empacct)
                                      (tRef dept)
                                      (joinEqCond (att2attrQualRel deptno_ empacct) 
                                                  (att2attrQualRel deptno_ dept)))))

-- 
-- 
-- #variants = 3
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ12_alt = empVQ12

-- temp0 = ρ (temp0) 
--           (π (managerno, deptno)
--              (ρ (temp) (σ (empno=10004) empacct) ⋈_{temp.deptno=dept.deptno} dept))
-- π (managerno^{v_3 ∨ v_4 ∨ v_5}, deptno^{v_3 ∨ v_4 ∨ v_5})
--   (temp0 ⋈_{temp0.managerno=dept.mangerno} dept)
-- 
-- #variants = 3
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ12_old = 
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
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
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

-- #variants = 1
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ13_alt = empVQ13

-- 14.intent: For all managers, find all managers in the department that he/she worked in, 
--            for VDB variants \vThree\ to \vFive.
--
-- #variants = 3
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
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

-- #variants = 3
-- #unique_variants = 1
-- 
-- after pushing schema: #variants = 
-- after pushing schema: #unique_variants = 
-- 
empVQ14_alt = empVQ14